// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: Lean.Elab.BuiltinDo.Basic Lean.Parser.Do Init.Control.Do Lean.Meta.ProdN
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
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::lean_st_ref_get;
use crate::ffi::lean_infer_type;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [83, 116, 100, 46, 116, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject,13215525487457488549 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value) as *mut crate::leanh::LeanObject,7754083906429771139 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject,13029182796945285130 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 95, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value) as *mut crate::leanh::LeanObject,16096857990383608286 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 111, 76, 101, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 77, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 116, 100, 46, 83, 116, 114, 101, 97, 109, 46, 110, 101, 120, 116, 63, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 101, 120, 116, 63, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value) as *mut crate::leanh::LeanObject,17138251589876785539 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value) as *mut crate::leanh::LeanObject,3899314177519732191 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut crate::leanh::LeanObject,17416048715816169289 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut crate::leanh::LeanObject,18184376426117065311 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut crate::leanh::LeanObject,9480010471355609749 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 66, 114, 101, 97, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 114, 101, 97, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut crate::leanh::LeanObject,15308379890181982757 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut crate::leanh::LeanObject,18184376426117065311 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut crate::leanh::LeanObject,4893146552088433753 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [115, 39, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value) as *mut crate::leanh::LeanObject,6632439502835183307 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 82, 101, 97, 115, 115, 105, 103, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 78, 111, 66, 105, 110, 100, 101, 114, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 78, 101, 115, 116, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value: crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [84, 104, 101, 32, 112, 114, 111, 111, 102, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 104, 101, 114, 101, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101, 110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 32, 121, 101, 116, 46, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 70, 111, 114, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,9513652089846993813 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 111, 70, 111, 114, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16953626593407929508 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__2_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value) as *mut crate::leanh::LeanObject,4570674678924417756 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value) as *mut crate::leanh::LeanObject,3326968124746134365 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value) as *mut crate::leanh::LeanObject,940684074193935882 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__6_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__7_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__8_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__9_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value) as *mut crate::leanh::LeanObject,4365236509002904093 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value) as *mut crate::leanh::LeanObject,9383794970646754147 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value) as *mut crate::leanh::LeanObject,13242179749370575553 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__15_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__15_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value) as *mut crate::leanh::LeanObject,18312965975140834652 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9833841078580172006 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value)
                as *mut crate::leanh::LeanObject,
            565778312915565143 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value: crate::leanh::LeanStringObject<44> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
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
            69, 97, 114, 108, 121, 32, 114, 101, 116, 117, 114, 110, 105, 110, 103, 32, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [121, 105, 101, 108, 100, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [70, 111, 114, 73, 110, 83, 116, 101, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8016886460890159001 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__8___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2981963283782553289 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value) as *mut crate::leanh::LeanObject,13286986945483979944 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [66, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [109, 97, 116, 99, 104, 95, 49, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value)
                as *mut crate::leanh::LeanObject,
            10906666425700568089 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value)
                as *mut crate::leanh::LeanObject,
            2052082663577137876 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12942615993048023751 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value)
                as *mut crate::leanh::LeanObject,
            15289851429949568889 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value)
                as *mut crate::leanh::LeanObject,
            8286241746160725162 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7877420268164864461 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5015202941514963680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [70, 111, 114, 73, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11398022837381273823 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 111, 114, 73, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11398022837381273823 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__2_value)
                as *mut crate::leanh::LeanObject,
            6704322920896662537 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7877420268164864461 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__5_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__5_value)
                as *mut crate::leanh::LeanObject,
            16646031496814324272 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__7_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [70, 111, 114, 73, 110, 39, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value)
                as *mut crate::leanh::LeanObject,
            8702119947958352715 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__9_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [102, 111, 114, 73, 110, 39, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value)
                as *mut crate::leanh::LeanObject,
            8702119947958352715 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__9_value)
                as *mut crate::leanh::LeanObject,
            6740408439742725642 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__11_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__11_value)
                as *mut crate::leanh::LeanObject,
            988715873908496486 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__13_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__13_value)
                as *mut crate::leanh::LeanObject,
            17734088147927324564 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__15_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__15_value)
                as *mut crate::leanh::LeanObject,
            6333055220850301478 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 68, 111, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut crate::leanh::LeanObject,102172329646148436 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value) as *mut crate::leanh::LeanObject,13250242672952379177 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_macroScope_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v_quotContext_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_3326_ = crate::leanh::lean_ctor_get(v___y_3325_, 0);
                v_traceMsgs_3327_ = crate::leanh::lean_ctor_get(v___y_3325_, 1);
                v_expandedMacroDecls_3328_ = crate::leanh::lean_ctor_get(v___y_3325_, 2);
                v_isSharedCheck_3341_ = (!crate::leanh::lean_is_exclusive(v___y_3325_)) as u8;
                if v_isSharedCheck_3341_ == 0 {
                    v___x_3330_ = v___y_3325_;
                    v_isShared_3331_ = v_isSharedCheck_3341_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_expandedMacroDecls_3328_);
                    crate::leanh::lean_inc(v_traceMsgs_3327_);
                    crate::leanh::lean_inc(v_macroScope_3326_);
                    crate::leanh::lean_dec(v___y_3325_);
                    v___x_3330_ = crate::leanh::lean_box(0);
                    v_isShared_3331_ = v_isSharedCheck_3341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_quotContext_3332_ = crate::leanh::lean_ctor_get(v___y_3324_, 1);
                v___x_3333_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1;
                v___x_3334_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3335_ = lean_nat_add(v_macroScope_3326_, v___x_3334_);
                if v_isShared_3331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3330_, 0, v___x_3335_);
                    v___x_3337_ = v___x_3330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_traceMsgs_3327_);
                    crate::leanh::lean_ctor_set(
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
                crate::leanh::lean_inc(v_quotContext_3332_);
                v___x_3338_ =
                    l_Lean_addMacroScope(v_quotContext_3332_, v___x_3333_, v_macroScope_3326_);
                v___x_3339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3339_, 0, v___x_3338_);
                crate::leanh::lean_ctor_set(v___x_3339_, 1, v___x_3337_);
                return v___x_3339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3344_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_3342_, v___y_3343_);
    crate::leanh::lean_dec_ref(v___y_3342_);
    return v_res_3344_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
    mut v_ref_3345_: *mut crate::leanh::LeanObject,
    mut v_canonical_3346_: u8,
    mut v___y_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3349_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_3347_, v___y_3348_);
                v_a_3350_ = crate::leanh::lean_ctor_get(v___x_3349_, 0);
                v_a_3351_ = crate::leanh::lean_ctor_get(v___x_3349_, 1);
                v_isSharedCheck_3359_ = (!crate::leanh::lean_is_exclusive(v___x_3349_)) as u8;
                if v_isSharedCheck_3359_ == 0 {
                    v___x_3353_ = v___x_3349_;
                    v_isShared_3354_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3351_);
                    crate::leanh::lean_inc(v_a_3350_);
                    crate::leanh::lean_dec(v___x_3349_);
                    v___x_3353_ = crate::leanh::lean_box(0);
                    v_isShared_3354_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3355_ = l_Lean_mkIdentFrom(v_ref_3345_, v_a_3350_, v_canonical_3346_);
                if v_isShared_3354_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3353_, 0, v___x_3355_);
                    v___x_3357_ = v___x_3353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_a_3351_);
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
    mut v_ref_3360_: *mut crate::leanh::LeanObject,
    mut v_canonical_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonical_boxed_3364_: u8 = 0;
    let mut v_res_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_3364_ = (crate::leanh::lean_unbox(v_canonical_3361_) as u8);
    v_res_3365_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
        v_ref_3360_,
        v_canonical_boxed_3364_,
        v___y_3362_,
        v___y_3363_,
    );
    crate::leanh::lean_dec_ref(v___y_3362_);
    crate::leanh::lean_dec(v_ref_3360_);
    return v_res_3365_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3;
    v___x_3371_ = l_String_toRawSubstring_x27(v___x_3370_);
    return v___x_3371_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3401_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32;
    v___x_3412_ = l_String_toRawSubstring_x27(v___x_3411_);
    return v___x_3412_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43;
    v___x_3431_ = l_String_toRawSubstring_x27(v___x_3430_);
    return v___x_3431_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53;
    v___x_3449_ = l_String_toRawSubstring_x27(v___x_3448_);
    return v___x_3449_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64;
    v___x_3469_ = l_String_toRawSubstring_x27(v___x_3468_);
    return v___x_3469_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69;
    v___x_3475_ = l_String_toRawSubstring_x27(v___x_3474_);
    return v___x_3475_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(
    mut v___x_3484_: *mut crate::leanh::LeanObject,
    mut v___x_3485_: *mut crate::leanh::LeanObject,
    mut v___x_3486_: *mut crate::leanh::LeanObject,
    mut v___x_3487_: u8,
    mut v___x_3488_: *mut crate::leanh::LeanObject,
    mut v___x_3489_: *mut crate::leanh::LeanObject,
    mut v___x_3490_: *mut crate::leanh::LeanObject,
    mut v___f_3491_: *mut crate::leanh::LeanObject,
    mut v_fst_3492_: *mut crate::leanh::LeanObject,
    mut v___x_3493_: *mut crate::leanh::LeanObject,
    mut v_snd_3494_: *mut crate::leanh::LeanObject,
    mut v_x_3495_: *mut crate::leanh::LeanObject,
    mut v_h_x3f_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v_a_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_reuseFailAlloc_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_val_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3499_ = l_Lean_Syntax_getArg(v___x_3484_, v___x_3485_);
                v___x_3500_ = l_Lean_Syntax_getArg(v___x_3484_, v___x_3486_);
                if crate::leanh::lean_obj_tag(v_h_x3f_3496_) == 1 {
                    v_val_3720_ = crate::leanh::lean_ctor_get(v_h_x3f_3496_, 0);
                    v___x_3721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77;
                    v___x_3722_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_val_3720_,
                        v___x_3721_,
                        v___y_3497_,
                        v___y_3498_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3722_) == 0 {
                        v_a_3723_ = crate::leanh::lean_ctor_get(v___x_3722_, 1);
                        crate::leanh::lean_inc(v_a_3723_);
                        crate::leanh::lean_dec_ref_known(v___x_3722_, 2);
                        v___y_3502_ = v_a_3723_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3500_);
                        crate::leanh::lean_dec(v___x_3499_);
                        crate::leanh::lean_dec(v_snd_3494_);
                        crate::leanh::lean_dec_ref(v___x_3493_);
                        crate::leanh::lean_dec(v_fst_3492_);
                        crate::leanh::lean_dec_ref(v___f_3491_);
                        crate::leanh::lean_dec_ref(v___x_3490_);
                        crate::leanh::lean_dec_ref(v___x_3489_);
                        crate::leanh::lean_dec_ref(v___x_3488_);
                        v_a_3724_ = crate::leanh::lean_ctor_get(v___x_3722_, 0);
                        v_a_3725_ = crate::leanh::lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3732_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3732_ == 0 {
                            v___x_3727_ = v___x_3722_;
                            v_isShared_3728_ = v_isSharedCheck_3732_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3725_);
                            crate::leanh::lean_inc(v_a_3724_);
                            crate::leanh::lean_dec(v___x_3722_);
                            v___x_3727_ = crate::leanh::lean_box(0);
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
                v_quotContext_3503_ = crate::leanh::lean_ctor_get(v___y_3497_, 1);
                v_currMacroScope_3504_ = crate::leanh::lean_ctor_get(v___y_3497_, 2);
                v_ref_3505_ = crate::leanh::lean_ctor_get(v___y_3497_, 5);
                v_ref_3506_ = l_Lean_replaceRef(v___x_3500_, v_ref_3505_);
                v___x_3507_ = l_Lean_SourceInfo_fromRef(v_ref_3506_, v___x_3487_);
                crate::leanh::lean_dec(v_ref_3506_);
                v___x_3508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0;
                crate::leanh::lean_inc_ref_n(v___x_3490_, 3);
                crate::leanh::lean_inc_ref_n(v___x_3489_, 3);
                crate::leanh::lean_inc_ref_n(v___x_3488_, 3);
                v___x_3509_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3508_);
                v___x_3510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1;
                v___x_3511_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3510_);
                v___x_3512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2;
                crate::leanh::lean_inc_n(v___x_3507_, 6);
                v___x_3513_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3507_);
                crate::leanh::lean_ctor_set(v___x_3513_, 1, v___x_3512_);
                v___x_3514_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
                v___x_3515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7;
                crate::leanh::lean_inc(v_currMacroScope_3504_);
                crate::leanh::lean_inc(v_quotContext_3503_);
                v___x_3516_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3515_, v_currMacroScope_3504_);
                v___x_3517_ = crate::leanh::lean_box(0);
                v___x_3518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11;
                v___x_3519_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3519_, 0, v___x_3507_);
                crate::leanh::lean_ctor_set(v___x_3519_, 1, v___x_3514_);
                crate::leanh::lean_ctor_set(v___x_3519_, 2, v___x_3516_);
                crate::leanh::lean_ctor_set(v___x_3519_, 3, v___x_3518_);
                crate::leanh::lean_inc(v___x_3511_);
                v___x_3520_ =
                    l_Lean_Syntax_node2(v___x_3507_, v___x_3511_, v___x_3513_, v___x_3519_);
                v___x_3521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_3522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14;
                v___x_3523_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3522_);
                v___x_3524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15;
                v___x_3525_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3525_, 0, v___x_3507_);
                crate::leanh::lean_ctor_set(v___x_3525_, 1, v___x_3524_);
                crate::leanh::lean_inc(v___x_3523_);
                v___x_3526_ = l_Lean_Syntax_node1(v___x_3507_, v___x_3523_, v___x_3525_);
                crate::leanh::lean_inc(v___x_3500_);
                crate::leanh::lean_inc_n(v___x_3526_, 2);
                v___x_3527_ = l_Lean_Syntax_node4(
                    v___x_3507_,
                    v___x_3521_,
                    v___x_3526_,
                    v___x_3526_,
                    v___x_3526_,
                    v___x_3500_,
                );
                v_macroScope_3528_ = crate::leanh::lean_ctor_get(v___y_3502_, 0);
                v_traceMsgs_3529_ = crate::leanh::lean_ctor_get(v___y_3502_, 1);
                v_expandedMacroDecls_3530_ = crate::leanh::lean_ctor_get(v___y_3502_, 2);
                v_isSharedCheck_3719_ = (!crate::leanh::lean_is_exclusive(v___y_3502_)) as u8;
                if v_isSharedCheck_3719_ == 0 {
                    v___x_3532_ = v___y_3502_;
                    v_isShared_3533_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_expandedMacroDecls_3530_);
                    crate::leanh::lean_inc(v_traceMsgs_3529_);
                    crate::leanh::lean_inc(v_macroScope_3528_);
                    crate::leanh::lean_dec(v___y_3502_);
                    v___x_3532_ = crate::leanh::lean_box(0);
                    v_isShared_3533_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3534_ = lean_nat_add(v_macroScope_3528_, v___x_3485_);
                if v_isShared_3533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3534_);
                    v___x_3536_ = v___x_3532_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_traceMsgs_3529_);
                    crate::leanh::lean_ctor_set(
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
                crate::leanh::lean_inc_ref(v___f_3491_);
                crate::leanh::lean_inc_ref(v___y_3497_);
                crate::leanh::lean_inc(v_ref_3505_);
                v___x_3537_ =
                    crate::leanh::lean_apply_3(v___f_3491_, v_ref_3505_, v___y_3497_, v___x_3536_);
                if crate::leanh::lean_obj_tag(v___x_3537_) == 0 {
                    v_a_3538_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                    crate::leanh::lean_inc_n(v_a_3538_, 9);
                    v_a_3539_ = crate::leanh::lean_ctor_get(v___x_3537_, 1);
                    crate::leanh::lean_inc(v_a_3539_);
                    crate::leanh::lean_dec_ref_known(v___x_3537_, 2);
                    crate::leanh::lean_inc(v___x_3509_);
                    v___x_3540_ =
                        l_Lean_Syntax_node2(v___x_3507_, v___x_3509_, v___x_3520_, v___x_3527_);
                    v___x_3541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17;
                    crate::leanh::lean_inc(v_quotContext_3503_);
                    v___x_3542_ =
                        l_Lean_addMacroScope(v_quotContext_3503_, v___x_3541_, v_macroScope_3528_);
                    v___x_3543_ = l_Lean_mkIdentFrom(v___x_3500_, v___x_3542_, v___x_3487_);
                    crate::leanh::lean_dec(v___x_3500_);
                    v___x_3544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18;
                    crate::leanh::lean_inc_ref_n(v___x_3490_, 6);
                    crate::leanh::lean_inc_ref_n(v___x_3489_, 6);
                    crate::leanh::lean_inc_ref_n(v___x_3488_, 6);
                    v___x_3545_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3544_);
                    v___x_3546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19;
                    v___x_3547_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3546_);
                    v___x_3548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20;
                    v___x_3549_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3549_, 0, v_a_3538_);
                    crate::leanh::lean_ctor_set(v___x_3549_, 1, v___x_3548_);
                    v___x_3550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21;
                    v___x_3551_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3551_, 0, v_a_3538_);
                    crate::leanh::lean_ctor_set(v___x_3551_, 1, v___x_3550_);
                    v___x_3552_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3521_, v___x_3551_);
                    v___x_3553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22;
                    v___x_3554_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3553_);
                    v___x_3555_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                    v___x_3556_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3556_, 0, v_a_3538_);
                    crate::leanh::lean_ctor_set(v___x_3556_, 1, v___x_3521_);
                    crate::leanh::lean_ctor_set(v___x_3556_, 2, v___x_3555_);
                    crate::leanh::lean_inc_ref_n(v___x_3556_, 3);
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
                    crate::leanh::lean_inc(v___x_3543_);
                    crate::leanh::lean_inc(v___x_3563_);
                    v___x_3564_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3563_, v___x_3543_);
                    v___x_3565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27;
                    v___x_3566_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3566_, 0, v_a_3538_);
                    crate::leanh::lean_ctor_set(v___x_3566_, 1, v___x_3565_);
                    v___x_3567_ = l_Lean_Syntax_node5(
                        v_a_3538_,
                        v___x_3561_,
                        v___x_3564_,
                        v___x_3556_,
                        v___x_3556_,
                        v___x_3566_,
                        v___x_3540_,
                    );
                    crate::leanh::lean_inc_ref(v___y_3497_);
                    crate::leanh::lean_inc(v_ref_3505_);
                    v___x_3568_ = crate::leanh::lean_apply_3(
                        v___f_3491_,
                        v_ref_3505_,
                        v___y_3497_,
                        v_a_3539_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3568_) == 0 {
                        v_a_3569_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                        v_a_3570_ = crate::leanh::lean_ctor_get(v___x_3568_, 1);
                        v_isSharedCheck_3699_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3568_)) as u8;
                        if v_isSharedCheck_3699_ == 0 {
                            v___x_3572_ = v___x_3568_;
                            v_isShared_3573_ = v_isSharedCheck_3699_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3570_);
                            crate::leanh::lean_inc(v_a_3569_);
                            crate::leanh::lean_dec(v___x_3568_);
                            v___x_3572_ = crate::leanh::lean_box(0);
                            v_isShared_3573_ = v_isSharedCheck_3699_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3567_);
                        crate::leanh::lean_dec(v___x_3563_);
                        crate::leanh::lean_dec(v___x_3559_);
                        crate::leanh::lean_dec(v___x_3557_);
                        crate::leanh::lean_dec_ref_known(v___x_3556_, 3);
                        crate::leanh::lean_dec(v___x_3552_);
                        crate::leanh::lean_dec_ref_known(v___x_3549_, 2);
                        crate::leanh::lean_dec(v___x_3547_);
                        crate::leanh::lean_dec(v___x_3545_);
                        crate::leanh::lean_dec(v___x_3543_);
                        crate::leanh::lean_dec(v_a_3538_);
                        crate::leanh::lean_dec(v___x_3523_);
                        crate::leanh::lean_dec(v___x_3511_);
                        crate::leanh::lean_dec(v___x_3509_);
                        crate::leanh::lean_dec(v___x_3499_);
                        crate::leanh::lean_dec(v_snd_3494_);
                        crate::leanh::lean_dec_ref(v___x_3493_);
                        crate::leanh::lean_dec(v_fst_3492_);
                        crate::leanh::lean_dec_ref(v___x_3490_);
                        crate::leanh::lean_dec_ref(v___x_3489_);
                        crate::leanh::lean_dec_ref(v___x_3488_);
                        v_a_3700_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                        v_a_3701_ = crate::leanh::lean_ctor_get(v___x_3568_, 1);
                        v_isSharedCheck_3708_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3568_)) as u8;
                        if v_isSharedCheck_3708_ == 0 {
                            v___x_3703_ = v___x_3568_;
                            v_isShared_3704_ = v_isSharedCheck_3708_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3701_);
                            crate::leanh::lean_inc(v_a_3700_);
                            crate::leanh::lean_dec(v___x_3568_);
                            v___x_3703_ = crate::leanh::lean_box(0);
                            v_isShared_3704_ = v_isSharedCheck_3708_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_macroScope_3528_);
                    crate::leanh::lean_dec(v___x_3527_);
                    crate::leanh::lean_dec(v___x_3523_);
                    crate::leanh::lean_dec(v___x_3520_);
                    crate::leanh::lean_dec(v___x_3511_);
                    crate::leanh::lean_dec(v___x_3509_);
                    crate::leanh::lean_dec(v___x_3507_);
                    crate::leanh::lean_dec(v___x_3500_);
                    crate::leanh::lean_dec(v___x_3499_);
                    crate::leanh::lean_dec(v_snd_3494_);
                    crate::leanh::lean_dec_ref(v___x_3493_);
                    crate::leanh::lean_dec(v_fst_3492_);
                    crate::leanh::lean_dec_ref(v___f_3491_);
                    crate::leanh::lean_dec_ref(v___x_3490_);
                    crate::leanh::lean_dec_ref(v___x_3489_);
                    crate::leanh::lean_dec_ref(v___x_3488_);
                    v_a_3709_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                    v_a_3710_ = crate::leanh::lean_ctor_get(v___x_3537_, 1);
                    v_isSharedCheck_3717_ = (!crate::leanh::lean_is_exclusive(v___x_3537_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3712_ = v___x_3537_;
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3710_);
                        crate::leanh::lean_inc(v_a_3709_);
                        crate::leanh::lean_dec(v___x_3537_);
                        v___x_3712_ = crate::leanh::lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc_n(v_a_3538_, 2);
                v___x_3574_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3559_, v___x_3567_);
                v___x_3575_ = l_Lean_Syntax_node4(
                    v_a_3538_,
                    v___x_3547_,
                    v___x_3549_,
                    v___x_3552_,
                    v___x_3557_,
                    v___x_3574_,
                );
                crate::leanh::lean_inc_n(v___x_3545_, 4);
                v___x_3576_ = l_Lean_Syntax_node2(v_a_3538_, v___x_3545_, v___x_3575_, v___x_3556_);
                v___x_3577_ = lean_array_push(v_fst_3492_, v___x_3576_);
                v___x_3578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28;
                crate::leanh::lean_inc_ref_n(v___x_3490_, 11);
                crate::leanh::lean_inc_ref_n(v___x_3489_, 11);
                crate::leanh::lean_inc_ref_n(v___x_3488_, 13);
                v___x_3579_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3578_);
                v___x_3580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29;
                v___x_3581_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3580_);
                v___x_3582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                crate::leanh::lean_inc_n(v_a_3569_, 54);
                v___x_3583_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3583_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3583_, 1, v___x_3582_);
                v___x_3584_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3584_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3584_, 1, v___x_3521_);
                crate::leanh::lean_ctor_set(v___x_3584_, 2, v___x_3555_);
                v___x_3585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31;
                v___x_3586_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3585_);
                v___x_3587_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3587_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3587_, 1, v___x_3512_);
                v___x_3588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
                v___x_3589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36;
                crate::leanh::lean_inc_n(v_currMacroScope_3504_, 5);
                crate::leanh::lean_inc_n(v_quotContext_3503_, 5);
                v___x_3590_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3589_, v_currMacroScope_3504_);
                v___x_3591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38;
                v___x_3592_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3592_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3592_, 1, v___x_3588_);
                crate::leanh::lean_ctor_set(v___x_3592_, 2, v___x_3590_);
                crate::leanh::lean_ctor_set(v___x_3592_, 3, v___x_3591_);
                v___x_3593_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3511_, v___x_3587_, v___x_3592_);
                v___x_3594_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3594_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3594_, 1, v___x_3524_);
                v___x_3595_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3523_, v___x_3594_);
                crate::leanh::lean_inc(v___x_3543_);
                crate::leanh::lean_inc_n(v___x_3595_, 2);
                v___x_3596_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3521_,
                    v___x_3595_,
                    v___x_3595_,
                    v___x_3595_,
                    v___x_3543_,
                );
                crate::leanh::lean_inc(v___x_3509_);
                v___x_3597_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3509_, v___x_3593_, v___x_3596_);
                crate::leanh::lean_inc_ref_n(v___x_3584_, 9);
                v___x_3598_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3586_, v___x_3584_, v___x_3597_);
                v___x_3599_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3598_);
                v___x_3600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                v___x_3601_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3601_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3601_, 1, v___x_3600_);
                v___x_3602_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40;
                v___x_3603_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3602_);
                v___x_3604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41;
                v___x_3605_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3604_);
                v___x_3606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                v___x_3607_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3607_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3607_, 1, v___x_3606_);
                v___x_3608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
                v___x_3609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45;
                v___x_3610_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3609_, v_currMacroScope_3504_);
                v___x_3611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49;
                v___x_3612_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3612_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3612_, 1, v___x_3608_);
                crate::leanh::lean_ctor_set(v___x_3612_, 2, v___x_3610_);
                crate::leanh::lean_ctor_set(v___x_3612_, 3, v___x_3611_);
                v___x_3613_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3612_);
                v___x_3614_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3613_);
                v___x_3615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                v___x_3616_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3616_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51;
                v___x_3618_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3617_);
                v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52;
                v___x_3620_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3620_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3620_, 1, v___x_3619_);
                v___x_3621_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3618_, v___x_3620_);
                v___x_3622_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3545_, v___x_3621_, v___x_3584_);
                v___x_3623_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3622_);
                crate::leanh::lean_inc_n(v___x_3579_, 2);
                v___x_3624_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3579_, v___x_3623_);
                crate::leanh::lean_inc_ref(v___x_3616_);
                crate::leanh::lean_inc_ref(v___x_3607_);
                crate::leanh::lean_inc(v___x_3605_);
                v___x_3625_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3605_,
                    v___x_3607_,
                    v___x_3614_,
                    v___x_3616_,
                    v___x_3624_,
                );
                v___x_3626_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
                v___x_3627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55;
                v___x_3628_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3627_, v_currMacroScope_3504_);
                v___x_3629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58;
                v___x_3630_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3630_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3630_, 1, v___x_3626_);
                crate::leanh::lean_ctor_set(v___x_3630_, 2, v___x_3628_);
                crate::leanh::lean_ctor_set(v___x_3630_, 3, v___x_3629_);
                v___x_3631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59;
                v___x_3632_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3631_);
                v___x_3633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60;
                v___x_3634_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3633_);
                v___x_3635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61;
                v___x_3636_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3636_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3636_, 1, v___x_3635_);
                v___x_3637_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63;
                v___x_3638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
                v___x_3639_ = crate::leanh::lean_box(0);
                v___x_3640_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3639_, v_currMacroScope_3504_);
                v___x_3641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66;
                v___x_3642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67;
                v___x_3643_ = l_Lean_Name_mkStr3(v___x_3488_, v___x_3641_, v___x_3642_);
                v___x_3644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                v___x_3645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68;
                v___x_3646_ = l_Lean_Name_mkStr2(v___x_3488_, v___x_3645_);
                v___x_3647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3647_, 0, v___x_3646_);
                v___x_3648_ = l_Lean_Name_mkStr3(v___x_3488_, v___x_3489_, v___x_3490_);
                v___x_3649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3649_, 0, v___x_3648_);
                v___x_3650_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3650_, 0, v___x_3649_);
                crate::leanh::lean_ctor_set(v___x_3650_, 1, v___x_3517_);
                v___x_3651_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3651_, 0, v___x_3647_);
                crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                v___x_3652_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3652_, 0, v___x_3644_);
                crate::leanh::lean_ctor_set(v___x_3652_, 1, v___x_3651_);
                v___x_3653_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3653_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3653_, 1, v___x_3638_);
                crate::leanh::lean_ctor_set(v___x_3653_, 2, v___x_3640_);
                crate::leanh::lean_ctor_set(v___x_3653_, 3, v___x_3652_);
                v___x_3654_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3637_, v___x_3653_);
                v___x_3655_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3634_, v___x_3636_, v___x_3654_);
                v___x_3656_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3656_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3656_, 1, v___x_3493_);
                v___x_3657_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
                v___x_3658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71;
                v___x_3659_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3658_, v_currMacroScope_3504_);
                v___x_3660_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3660_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3660_, 1, v___x_3657_);
                crate::leanh::lean_ctor_set(v___x_3660_, 2, v___x_3659_);
                crate::leanh::lean_ctor_set(v___x_3660_, 3, v___x_3517_);
                crate::leanh::lean_inc_ref(v___x_3660_);
                v___x_3661_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3660_);
                v___x_3662_ = l_Lean_Syntax_node3(
                    v_a_3569_,
                    v___x_3521_,
                    v___x_3499_,
                    v___x_3656_,
                    v___x_3661_,
                );
                v___x_3663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72;
                v___x_3664_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3664_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3664_, 1, v___x_3663_);
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
                v___x_3675_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3675_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3675_, 1, v___x_3565_);
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
                v___x_3682_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3682_, 0, v_a_3569_);
                crate::leanh::lean_ctor_set(v___x_3682_, 1, v___x_3681_);
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
                v___x_3694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3694_, 0, v___x_3577_);
                crate::leanh::lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                v___x_3695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3695_, 0, v___x_3694_);
                if v_isShared_3573_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3572_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3572_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_a_3570_);
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
                    v_reuseFailAlloc_3707_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_a_3701_);
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
                    v_reuseFailAlloc_3716_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_a_3710_);
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
                    v_reuseFailAlloc_3731_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_a_3725_);
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
    mut v___x_3733_: *mut crate::leanh::LeanObject,
    mut v___x_3734_: *mut crate::leanh::LeanObject,
    mut v___x_3735_: *mut crate::leanh::LeanObject,
    mut v___x_3736_: *mut crate::leanh::LeanObject,
    mut v___x_3737_: *mut crate::leanh::LeanObject,
    mut v___x_3738_: *mut crate::leanh::LeanObject,
    mut v___x_3739_: *mut crate::leanh::LeanObject,
    mut v___f_3740_: *mut crate::leanh::LeanObject,
    mut v_fst_3741_: *mut crate::leanh::LeanObject,
    mut v___x_3742_: *mut crate::leanh::LeanObject,
    mut v_snd_3743_: *mut crate::leanh::LeanObject,
    mut v_x_3744_: *mut crate::leanh::LeanObject,
    mut v_h_x3f_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_146124__boxed_3748_: u8 = 0;
    let mut v_res_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146124__boxed_3748_ = (crate::leanh::lean_unbox(v___x_3736_) as u8);
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
    crate::leanh::lean_dec_ref(v___y_3746_);
    crate::leanh::lean_dec(v_h_x3f_3745_);
    crate::leanh::lean_dec(v___x_3735_);
    crate::leanh::lean_dec(v___x_3734_);
    crate::leanh::lean_dec(v___x_3733_);
    return v_res_3749_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(
    mut v___x_3750_: u8,
    mut v_____do__lift_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3751_, v___x_3750_);
    v___x_3755_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3754_);
    crate::leanh::lean_ctor_set(v___x_3755_, 1, v___y_3753_);
    return v___x_3755_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(
    mut v___x_3756_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_146730__boxed_3760_: u8 = 0;
    let mut v_res_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146730__boxed_3760_ = (crate::leanh::lean_unbox(v___x_3756_) as u8);
    v_res_3761_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(
            v___x_146730__boxed_3760_,
            v_____do__lift_3757_,
            v___y_3758_,
            v___y_3759_,
        );
    crate::leanh::lean_dec_ref(v___y_3758_);
    crate::leanh::lean_dec(v_____do__lift_3757_);
    return v_res_3761_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
    mut v___x_3772_: u8,
    mut v_a_3773_: *mut crate::leanh::LeanObject,
    mut v_b_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: u8 = 0;
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v_a_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v_unused_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3777_ = crate::leanh::lean_ctor_get(v_a_3773_, 0);
                v_start_3778_ = crate::leanh::lean_ctor_get(v_a_3773_, 1);
                v_stop_3779_ = crate::leanh::lean_ctor_get(v_a_3773_, 2);
                v_isSharedCheck_3873_ = (!crate::leanh::lean_is_exclusive(v_a_3773_)) as u8;
                if v_isSharedCheck_3873_ == 0 {
                    v___x_3781_ = v_a_3773_;
                    v_isShared_3782_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_3779_);
                    crate::leanh::lean_inc(v_start_3778_);
                    crate::leanh::lean_inc(v_array_3777_);
                    crate::leanh::lean_dec(v_a_3773_);
                    v___x_3781_ = crate::leanh::lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3783_ = lean_nat_dec_lt(v_start_3778_, v_stop_3779_);
                if v___x_3783_ == 0 {
                    crate::leanh::lean_del_object(v___x_3781_);
                    crate::leanh::lean_dec(v_stop_3779_);
                    crate::leanh::lean_dec(v_start_3778_);
                    crate::leanh::lean_dec_ref(v_array_3777_);
                    v___x_3784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3784_, 0, v_b_3774_);
                    crate::leanh::lean_ctor_set(v___x_3784_, 1, v___y_3776_);
                    return v___x_3784_;
                } else {
                    v_fst_3785_ = crate::leanh::lean_ctor_get(v_b_3774_, 0);
                    v_snd_3786_ = crate::leanh::lean_ctor_get(v_b_3774_, 1);
                    v_isSharedCheck_3872_ = (!crate::leanh::lean_is_exclusive(v_b_3774_)) as u8;
                    if v_isSharedCheck_3872_ == 0 {
                        v___x_3788_ = v_b_3774_;
                        v_isShared_3789_ = v_isSharedCheck_3872_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3786_);
                        crate::leanh::lean_inc(v_fst_3785_);
                        crate::leanh::lean_dec(v_b_3774_);
                        v___x_3788_ = crate::leanh::lean_box(0);
                        v_isShared_3789_ = v_isSharedCheck_3872_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3790_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0;
                v___x_3792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1;
                v___x_3793_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2;
                v___x_3794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                v___x_3795_ = lean_nat_add(v_start_3778_, v___x_3790_);
                crate::leanh::lean_inc_ref(v_array_3777_);
                if v_isShared_3782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3781_, 1, v___x_3795_);
                    v___x_3797_ = v___x_3781_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3871_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_array_3777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_stop_3779_);
                    v___x_3797_ = v_reuseFailAlloc_3871_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3823_ = lean_array_fget(v_array_3777_, v_start_3778_);
                crate::leanh::lean_dec(v_start_3778_);
                crate::leanh::lean_dec_ref(v_array_3777_);
                crate::leanh::lean_inc(v___x_3823_);
                v___x_3824_ = l_Lean_Syntax_isOfKind(v___x_3823_, v___x_3794_);
                if v___x_3824_ == 0 {
                    crate::leanh::lean_dec(v___x_3823_);
                    v___x_3825_ = l_Lean_Macro_throwUnsupported___redArg(v___y_3776_);
                    if crate::leanh::lean_obj_tag(v___x_3825_) == 0 {
                        v_a_3826_ = crate::leanh::lean_ctor_get(v___x_3825_, 1);
                        crate::leanh::lean_inc(v_a_3826_);
                        crate::leanh::lean_dec_ref_known(v___x_3825_, 2);
                        if v_isShared_3789_ == 0 {
                            v___x_3828_ = v___x_3788_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3830_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_fst_3785_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_snd_3786_);
                            v___x_3828_ = v_reuseFailAlloc_3830_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3797_);
                        crate::leanh::lean_del_object(v___x_3788_);
                        crate::leanh::lean_dec(v_snd_3786_);
                        crate::leanh::lean_dec(v_fst_3785_);
                        v_a_3831_ = crate::leanh::lean_ctor_get(v___x_3825_, 0);
                        v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3825_, 1);
                        v_isSharedCheck_3839_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3825_)) as u8;
                        if v_isSharedCheck_3839_ == 0 {
                            v___x_3834_ = v___x_3825_;
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3832_);
                            crate::leanh::lean_inc(v_a_3831_);
                            crate::leanh::lean_dec(v___x_3825_);
                            v___x_3834_ = crate::leanh::lean_box(0);
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v___x_3840_ = crate::leanh::lean_box((v___x_3772_) as usize);
                    v___f_3841_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                    crate::leanh::lean_closure_set(v___f_3841_, 0, v___x_3840_);
                    v___x_3842_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5;
                    v___x_3844_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3845_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3844_);
                    v___x_3846_ = l_Lean_Syntax_isNone(v___x_3845_);
                    if v___x_3846_ == 0 {
                        v___x_3847_ = crate::leanh::lean_unsigned_to_nat(2);
                        crate::leanh::lean_inc(v___x_3845_);
                        v___x_3848_ = l_Lean_Syntax_matchesNull(v___x_3845_, v___x_3847_);
                        if v___x_3848_ == 0 {
                            crate::leanh::lean_dec(v___x_3845_);
                            crate::leanh::lean_dec_ref(v___f_3841_);
                            crate::leanh::lean_dec(v___x_3823_);
                            v___x_3849_ = l_Lean_Macro_throwUnsupported___redArg(v___y_3776_);
                            if crate::leanh::lean_obj_tag(v___x_3849_) == 0 {
                                v_a_3850_ = crate::leanh::lean_ctor_get(v___x_3849_, 1);
                                crate::leanh::lean_inc(v_a_3850_);
                                crate::leanh::lean_dec_ref_known(v___x_3849_, 2);
                                if v_isShared_3789_ == 0 {
                                    v___x_3852_ = v___x_3788_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3854_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3854_,
                                        0,
                                        v_fst_3785_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3854_,
                                        1,
                                        v_snd_3786_,
                                    );
                                    v___x_3852_ = v_reuseFailAlloc_3854_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3797_);
                                crate::leanh::lean_del_object(v___x_3788_);
                                crate::leanh::lean_dec(v_snd_3786_);
                                crate::leanh::lean_dec(v_fst_3785_);
                                v_a_3855_ = crate::leanh::lean_ctor_get(v___x_3849_, 0);
                                v_a_3856_ = crate::leanh::lean_ctor_get(v___x_3849_, 1);
                                v_isSharedCheck_3863_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3849_)) as u8;
                                if v_isSharedCheck_3863_ == 0 {
                                    v___x_3858_ = v___x_3849_;
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3856_);
                                    crate::leanh::lean_inc(v_a_3855_);
                                    crate::leanh::lean_dec(v___x_3849_);
                                    v___x_3858_ = crate::leanh::lean_box(0);
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3788_);
                            v___x_3864_ = l_Lean_Syntax_getArg(v___x_3845_, v___x_3844_);
                            crate::leanh::lean_dec(v___x_3845_);
                            v___x_3865_ = crate::leanh::lean_box(0);
                            v___x_3866_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                            v___x_3867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_3823_, v___x_3790_, v___x_3842_, v___x_3772_, v___x_3791_, v___x_3792_, v___x_3793_, v___f_3841_, v_fst_3785_, v___x_3843_, v_snd_3786_, v___x_3865_, v___x_3866_, v___y_3775_, v___y_3776_);
                            crate::leanh::lean_dec_ref_known(v___x_3866_, 1);
                            crate::leanh::lean_dec(v___x_3823_);
                            v___y_3799_ = v___x_3867_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3845_);
                        crate::leanh::lean_del_object(v___x_3788_);
                        v___x_3868_ = crate::leanh::lean_box(0);
                        v___x_3869_ = crate::leanh::lean_box(0);
                        v___x_3870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_3823_, v___x_3790_, v___x_3842_, v___x_3772_, v___x_3791_, v___x_3792_, v___x_3793_, v___f_3841_, v_fst_3785_, v___x_3843_, v_snd_3786_, v___x_3868_, v___x_3869_, v___y_3775_, v___y_3776_);
                        crate::leanh::lean_dec(v___x_3823_);
                        v___y_3799_ = v___x_3870_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_3799_) == 0 {
                    v_a_3800_ = crate::leanh::lean_ctor_get(v___y_3799_, 0);
                    crate::leanh::lean_inc(v_a_3800_);
                    if crate::leanh::lean_obj_tag(v_a_3800_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_3797_);
                        v_a_3801_ = crate::leanh::lean_ctor_get(v___y_3799_, 1);
                        v_isSharedCheck_3809_ =
                            (!crate::leanh::lean_is_exclusive(v___y_3799_)) as u8;
                        if v_isSharedCheck_3809_ == 0 {
                            v_unused_3810_ = crate::leanh::lean_ctor_get(v___y_3799_, 0);
                            crate::leanh::lean_dec(v_unused_3810_);
                            v___x_3803_ = v___y_3799_;
                            v_isShared_3804_ = v_isSharedCheck_3809_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3801_);
                            crate::leanh::lean_dec(v___y_3799_);
                            v___x_3803_ = crate::leanh::lean_box(0);
                            v_isShared_3804_ = v_isSharedCheck_3809_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_3811_ = crate::leanh::lean_ctor_get(v___y_3799_, 1);
                        crate::leanh::lean_inc(v_a_3811_);
                        crate::leanh::lean_dec_ref_known(v___y_3799_, 2);
                        v_a_3812_ = crate::leanh::lean_ctor_get(v_a_3800_, 0);
                        crate::leanh::lean_inc(v_a_3812_);
                        crate::leanh::lean_dec_ref_known(v_a_3800_, 1);
                        v_a_3773_ = v___x_3797_;
                        v_b_3774_ = v_a_3812_;
                        v___y_3776_ = v_a_3811_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3797_);
                    v_a_3814_ = crate::leanh::lean_ctor_get(v___y_3799_, 0);
                    v_a_3815_ = crate::leanh::lean_ctor_get(v___y_3799_, 1);
                    v_isSharedCheck_3822_ = (!crate::leanh::lean_is_exclusive(v___y_3799_)) as u8;
                    if v_isSharedCheck_3822_ == 0 {
                        v___x_3817_ = v___y_3799_;
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3815_);
                        crate::leanh::lean_inc(v_a_3814_);
                        crate::leanh::lean_dec(v___y_3799_);
                        v___x_3817_ = crate::leanh::lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_a_3805_ = crate::leanh::lean_ctor_get(v_a_3800_, 0);
                crate::leanh::lean_inc(v_a_3805_);
                crate::leanh::lean_dec_ref_known(v_a_3800_, 1);
                if v_isShared_3804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3803_, 0, v_a_3805_);
                    v___x_3807_ = v___x_3803_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_a_3801_);
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
                    v_reuseFailAlloc_3821_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_a_3815_);
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
                    v_reuseFailAlloc_3838_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_a_3832_);
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
                    v_reuseFailAlloc_3862_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3856_);
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
    mut v___x_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
    mut v_b_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
    mut v___y_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_146766__boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_146766__boxed_3879_ = (crate::leanh::lean_unbox(v___x_3874_) as u8);
    v_res_3880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
        v___x_146766__boxed_3879_,
        v_a_3875_,
        v_b_3876_,
        v___y_3877_,
        v___y_3878_,
    );
    crate::leanh::lean_dec_ref(v___y_3877_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_Elab_Do_expandDoFor(
    mut v_stx_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_ref_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4016_: u8 = 0;
    let mut v_a_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4095_: u8 = 0;
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4173_: u8 = 0;
    let mut v_x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v_ref_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v___y_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: u8 = 0;
    let mut v___y_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v___y_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v_decls_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    let mut v_decls_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_ref_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4374_: u8 = 0;
    let mut v_a_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v_decls_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4486_: u8 = 0;
    let mut v_ref_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_a_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4511_: u8 = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4581_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: u8 = 0;
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3940_ = l_Lean_Elab_Do_expandDoFor___closed__1;
                crate::leanh::lean_inc(v_stx_3937_);
                v___x_3941_ = l_Lean_Syntax_isOfKind(v_stx_3937_, v___x_3940_);
                if v___x_3941_ == 0 {
                    crate::leanh::lean_dec(v_stx_3937_);
                    v___x_3942_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                    return v___x_3942_;
                } else {
                    v___x_3943_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_3944_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_3943_);
                    v___x_3945_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3946_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_3945_);
                    crate::leanh::lean_inc(v___x_3946_);
                    v___x_3947_ = l_Lean_Syntax_matchesNull(v___x_3946_, v___x_3945_);
                    if v___x_3947_ == 0 {
                        v___x_3948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        v_decls_3980_ = l_Lean_Syntax_getArgs(v___x_3946_);
                        crate::leanh::lean_dec(v___x_3946_);
                        v_decls_3981_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_3980_);
                        crate::leanh::lean_dec_ref(v_decls_3980_);
                        v___x_4026_ = crate::leanh::lean_box(0);
                        v___x_4027_ = lean_array_get(v___x_4026_, v_decls_3981_, v___x_3943_);
                        crate::leanh::lean_inc(v___x_4027_);
                        v___x_4028_ = l_Lean_Syntax_isOfKind(v___x_4027_, v___x_3948_);
                        if v___x_4028_ == 0 {
                            crate::leanh::lean_dec(v___x_4027_);
                            crate::leanh::lean_dec_ref(v_decls_3981_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            crate::leanh::lean_dec(v_stx_3937_);
                            v___x_4029_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                            return v___x_4029_;
                        } else {
                            v___x_4030_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_body_4031_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4030_);
                            crate::leanh::lean_dec(v_stx_3937_);
                            v___x_4096_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_3943_);
                            v___x_4097_ = l_Lean_Syntax_isNone(v___x_4096_);
                            if v___x_4097_ == 0 {
                                v___x_4098_ = crate::leanh::lean_unsigned_to_nat(2);
                                crate::leanh::lean_inc(v___x_4096_);
                                v___x_4099_ = l_Lean_Syntax_matchesNull(v___x_4096_, v___x_4098_);
                                if v___x_4099_ == 0 {
                                    crate::leanh::lean_dec(v___x_4096_);
                                    crate::leanh::lean_dec(v_body_4031_);
                                    crate::leanh::lean_dec(v___x_4027_);
                                    crate::leanh::lean_dec_ref(v_decls_3981_);
                                    crate::leanh::lean_dec(v_tk_3944_);
                                    v___x_4100_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                    return v___x_4100_;
                                } else {
                                    v_h_x3f_4101_ = l_Lean_Syntax_getArg(v___x_4096_, v___x_3943_);
                                    crate::leanh::lean_dec(v___x_4096_);
                                    v___x_4102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4102_, 0, v_h_x3f_4101_);
                                    v_h_x3f_4033_ = v___x_4102_;
                                    v___y_4034_ = v_a_3938_;
                                    v___y_4035_ = v_a_3939_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4096_);
                                v___x_4103_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_inc(v___x_4104_);
                        v___x_4337_ = l_Lean_Syntax_isOfKind(v___x_4104_, v___x_4105_);
                        if v___x_4337_ == 0 {
                            crate::leanh::lean_dec(v___x_4104_);
                            v_decls_4338_ = l_Lean_Syntax_getArgs(v___x_3946_);
                            crate::leanh::lean_dec(v___x_3946_);
                            v_decls_4339_ =
                                l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4338_);
                            crate::leanh::lean_dec_ref(v_decls_4338_);
                            v___x_4384_ = crate::leanh::lean_box(0);
                            v___x_4385_ = lean_array_get(v___x_4384_, v_decls_4339_, v___x_3943_);
                            crate::leanh::lean_inc(v___x_4385_);
                            v___x_4386_ = l_Lean_Syntax_isOfKind(v___x_4385_, v___x_4105_);
                            if v___x_4386_ == 0 {
                                crate::leanh::lean_dec(v___x_4385_);
                                crate::leanh::lean_dec_ref(v_decls_4339_);
                                crate::leanh::lean_dec(v_tk_3944_);
                                crate::leanh::lean_dec(v_stx_3937_);
                                v___x_4387_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                return v___x_4387_;
                            } else {
                                v___x_4388_ = crate::leanh::lean_unsigned_to_nat(3);
                                v_body_4389_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4388_);
                                crate::leanh::lean_dec(v_stx_3937_);
                                v___x_4454_ = l_Lean_Syntax_getArg(v___x_4385_, v___x_3943_);
                                v___x_4455_ = l_Lean_Syntax_isNone(v___x_4454_);
                                if v___x_4455_ == 0 {
                                    v___x_4456_ = crate::leanh::lean_unsigned_to_nat(2);
                                    crate::leanh::lean_inc(v___x_4454_);
                                    v___x_4457_ =
                                        l_Lean_Syntax_matchesNull(v___x_4454_, v___x_4456_);
                                    if v___x_4457_ == 0 {
                                        crate::leanh::lean_dec(v___x_4454_);
                                        crate::leanh::lean_dec(v_body_4389_);
                                        crate::leanh::lean_dec(v___x_4385_);
                                        crate::leanh::lean_dec_ref(v_decls_4339_);
                                        crate::leanh::lean_dec(v_tk_3944_);
                                        v___x_4458_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                        return v___x_4458_;
                                    } else {
                                        v_h_x3f_4459_ =
                                            l_Lean_Syntax_getArg(v___x_4454_, v___x_3943_);
                                        crate::leanh::lean_dec(v___x_4454_);
                                        v___x_4460_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4460_, 0, v_h_x3f_4459_);
                                        v_h_x3f_4391_ = v___x_4460_;
                                        v___y_4392_ = v_a_3938_;
                                        v___y_4393_ = v_a_3939_;
                                        state = 31;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_4454_);
                                    v___x_4461_ = crate::leanh::lean_box(0);
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
                                v___x_4464_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_4465_ = l_Lean_Syntax_matchesNull(v___x_4462_, v___x_4464_);
                                if v___x_4465_ == 0 {
                                    crate::leanh::lean_dec(v___x_4104_);
                                    v_decls_4466_ = l_Lean_Syntax_getArgs(v___x_3946_);
                                    crate::leanh::lean_dec(v___x_3946_);
                                    v_decls_4467_ =
                                        l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4466_);
                                    crate::leanh::lean_dec_ref(v_decls_4466_);
                                    v___x_4512_ = crate::leanh::lean_box(0);
                                    v___x_4513_ =
                                        lean_array_get(v___x_4512_, v_decls_4467_, v___x_3943_);
                                    crate::leanh::lean_inc(v___x_4513_);
                                    v___x_4514_ = l_Lean_Syntax_isOfKind(v___x_4513_, v___x_4105_);
                                    if v___x_4514_ == 0 {
                                        crate::leanh::lean_dec(v___x_4513_);
                                        crate::leanh::lean_dec_ref(v_decls_4467_);
                                        crate::leanh::lean_dec(v_tk_3944_);
                                        crate::leanh::lean_dec(v_stx_3937_);
                                        v___x_4515_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                        return v___x_4515_;
                                    } else {
                                        v___x_4516_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v_body_4517_ =
                                            l_Lean_Syntax_getArg(v_stx_3937_, v___x_4516_);
                                        crate::leanh::lean_dec(v_stx_3937_);
                                        v___x_4582_ =
                                            l_Lean_Syntax_getArg(v___x_4513_, v___x_3943_);
                                        v___x_4583_ = l_Lean_Syntax_isNone(v___x_4582_);
                                        if v___x_4583_ == 0 {
                                            crate::leanh::lean_inc(v___x_4582_);
                                            v___x_4584_ =
                                                l_Lean_Syntax_matchesNull(v___x_4582_, v___x_4464_);
                                            if v___x_4584_ == 0 {
                                                crate::leanh::lean_dec(v___x_4582_);
                                                crate::leanh::lean_dec(v_body_4517_);
                                                crate::leanh::lean_dec(v___x_4513_);
                                                crate::leanh::lean_dec_ref(v_decls_4467_);
                                                crate::leanh::lean_dec(v_tk_3944_);
                                                v___x_4585_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v_a_3939_,
                                                    );
                                                return v___x_4585_;
                                            } else {
                                                v_h_x3f_4586_ =
                                                    l_Lean_Syntax_getArg(v___x_4582_, v___x_3943_);
                                                crate::leanh::lean_dec(v___x_4582_);
                                                v___x_4587_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
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
                                            crate::leanh::lean_dec(v___x_4582_);
                                            v___x_4588_ = crate::leanh::lean_box(0);
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
                                crate::leanh::lean_dec(v___x_4462_);
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
                crate::leanh::lean_inc_ref_n(v___y_3953_, 3);
                v___x_3961_ = l_Array_append___redArg(v___y_3953_, v___y_3960_);
                crate::leanh::lean_dec_ref(v___y_3960_);
                crate::leanh::lean_inc_n(v___y_3959_, 4);
                crate::leanh::lean_inc_n(v___y_3952_, 10);
                v___x_3962_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3962_, 0, v___y_3952_);
                crate::leanh::lean_ctor_set(v___x_3962_, 1, v___y_3959_);
                crate::leanh::lean_ctor_set(v___x_3962_, 2, v___x_3961_);
                v___x_3963_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_3964_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3964_, 0, v___y_3952_);
                crate::leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
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
                v___x_3968_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3968_, 0, v___y_3952_);
                crate::leanh::lean_ctor_set(v___x_3968_, 1, v___x_3967_);
                crate::leanh::lean_inc_ref(v___x_3968_);
                v___x_3969_ = l_Lean_Syntax_node4(
                    v___y_3952_,
                    v___x_3940_,
                    v___y_3958_,
                    v___x_3966_,
                    v___x_3968_,
                    v___y_3950_,
                );
                v___x_3970_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3970_, 0, v___y_3952_);
                crate::leanh::lean_ctor_set(v___x_3970_, 1, v___y_3959_);
                crate::leanh::lean_ctor_set(v___x_3970_, 2, v___y_3953_);
                crate::leanh::lean_inc(v___y_3957_);
                v___x_3971_ =
                    l_Lean_Syntax_node2(v___y_3952_, v___y_3957_, v___x_3969_, v___x_3970_);
                v___x_3972_ = lean_array_push(v___y_3956_, v___x_3971_);
                v___x_3973_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_3974_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_3975_ = l_Array_append___redArg(v___y_3953_, v___x_3972_);
                crate::leanh::lean_dec_ref(v___x_3972_);
                v___x_3976_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3976_, 0, v___y_3952_);
                crate::leanh::lean_ctor_set(v___x_3976_, 1, v___y_3959_);
                crate::leanh::lean_ctor_set(v___x_3976_, 2, v___x_3975_);
                v___x_3977_ = l_Lean_Syntax_node1(v___y_3952_, v___x_3974_, v___x_3976_);
                v___x_3978_ =
                    l_Lean_Syntax_node2(v___y_3952_, v___x_3973_, v___x_3968_, v___x_3977_);
                v___x_3979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3979_, 0, v___x_3978_);
                crate::leanh::lean_ctor_set(v___x_3979_, 1, v___y_3955_);
                return v___x_3979_;
            }
            2 => {
                v___x_3990_ = lean_array_get_size(v_decls_3981_);
                v___x_3991_ = l_Array_toSubarray___redArg(v_decls_3981_, v___x_3945_, v___x_3990_);
                crate::leanh::lean_inc_ref(v___y_3983_);
                v___x_3992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3992_, 0, v___y_3983_);
                crate::leanh::lean_ctor_set(v___x_3992_, 1, v_body_3987_);
                v___x_3993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_3947_, v___x_3991_, v___x_3992_, v___y_3988_, v___y_3989_);
                if crate::leanh::lean_obj_tag(v___x_3993_) == 0 {
                    v_a_3994_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                    crate::leanh::lean_inc(v_a_3994_);
                    v_a_3995_ = crate::leanh::lean_ctor_get(v___x_3993_, 1);
                    crate::leanh::lean_inc(v_a_3995_);
                    crate::leanh::lean_dec_ref_known(v___x_3993_, 2);
                    v_fst_3996_ = crate::leanh::lean_ctor_get(v_a_3994_, 0);
                    v_snd_3997_ = crate::leanh::lean_ctor_get(v_a_3994_, 1);
                    v_isSharedCheck_4016_ = (!crate::leanh::lean_is_exclusive(v_a_3994_)) as u8;
                    if v_isSharedCheck_4016_ == 0 {
                        v___x_3999_ = v_a_3994_;
                        v_isShared_4000_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3997_);
                        crate::leanh::lean_inc(v_fst_3996_);
                        crate::leanh::lean_dec(v_a_3994_);
                        v___x_3999_ = crate::leanh::lean_box(0);
                        v_isShared_4000_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3986_);
                    crate::leanh::lean_dec(v___y_3985_);
                    crate::leanh::lean_dec(v___y_3984_);
                    crate::leanh::lean_dec(v_tk_3944_);
                    v_a_4017_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                    v_a_4018_ = crate::leanh::lean_ctor_get(v___x_3993_, 1);
                    v_isSharedCheck_4025_ = (!crate::leanh::lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4025_ == 0 {
                        v___x_4020_ = v___x_3993_;
                        v_isShared_4021_ = v_isSharedCheck_4025_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4018_);
                        crate::leanh::lean_inc(v_a_4017_);
                        crate::leanh::lean_dec(v___x_3993_);
                        v___x_4020_ = crate::leanh::lean_box(0);
                        v_isShared_4021_ = v_isSharedCheck_4025_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_4001_ = crate::leanh::lean_ctor_get(v___y_3988_, 5);
                v___x_4002_ = l_Lean_SourceInfo_fromRef(v_ref_4001_, v___x_3947_);
                v___x_4003_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4004_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                crate::leanh::lean_dec(v_tk_3944_);
                v___x_4005_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4000_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3999_, 2);
                    crate::leanh::lean_ctor_set(v___x_3999_, 1, v___x_4005_);
                    crate::leanh::lean_ctor_set(v___x_3999_, 0, v___x_4004_);
                    v___x_4007_ = v___x_3999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4015_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if crate::leanh::lean_obj_tag(v___y_3985_) == 1 {
                    v_val_4010_ = crate::leanh::lean_ctor_get(v___y_3985_, 0);
                    crate::leanh::lean_inc(v_val_4010_);
                    crate::leanh::lean_dec_ref_known(v___y_3985_, 1);
                    v___x_4011_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    crate::leanh::lean_inc(v___x_4002_);
                    v___x_4012_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4012_, 0, v___x_4002_);
                    crate::leanh::lean_ctor_set(v___x_4012_, 1, v___x_4011_);
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
                    crate::leanh::lean_dec(v___y_3985_);
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
                    v_reuseFailAlloc_4024_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_a_4018_);
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
                crate::leanh::lean_dec(v___x_4027_);
                v_doElems_4038_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4039_ = l_Lean_Syntax_isIdent(v___x_4036_);
                if v___x_4039_ == 0 {
                    v___x_4040_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    crate::leanh::lean_inc(v___x_4036_);
                    v___x_4041_ = l_Lean_Syntax_isOfKind(v___x_4036_, v___x_4040_);
                    if v___x_4041_ == 0 {
                        v___x_4042_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4036_,
                                v___x_4041_,
                                v___y_4034_,
                                v___y_4035_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4042_) == 0 {
                            v_a_4043_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                            crate::leanh::lean_inc_n(v_a_4043_, 2);
                            v_a_4044_ = crate::leanh::lean_ctor_get(v___x_4042_, 1);
                            crate::leanh::lean_inc(v_a_4044_);
                            crate::leanh::lean_dec_ref_known(v___x_4042_, 2);
                            v_ref_4045_ = crate::leanh::lean_ctor_get(v___y_4034_, 5);
                            v___x_4046_ = l_Lean_SourceInfo_fromRef(v_ref_4045_, v___x_4041_);
                            v___x_4047_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4049_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4050_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            crate::leanh::lean_inc_n(v___x_4046_, 15);
                            v___x_4052_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4052_, 0, v___x_4046_);
                            crate::leanh::lean_ctor_set(v___x_4052_, 1, v___x_4051_);
                            v___x_4053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4054_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4046_);
                            crate::leanh::lean_ctor_set(v___x_4054_, 1, v___x_4048_);
                            crate::leanh::lean_ctor_set(v___x_4054_, 2, v___x_4053_);
                            v___x_4055_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            crate::leanh::lean_inc_ref_n(v___x_4054_, 4);
                            v___x_4056_ = l_Lean_Syntax_node2(
                                v___x_4046_,
                                v___x_4055_,
                                v___x_4054_,
                                v_a_4043_,
                            );
                            v___x_4057_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4056_);
                            v___x_4058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4059_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4046_);
                            crate::leanh::lean_ctor_set(v___x_4059_, 1, v___x_4058_);
                            v___x_4060_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4061_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4063_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4046_);
                            crate::leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                            v___x_4064_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4036_);
                            v___x_4065_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4064_);
                            v___x_4066_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4067_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4067_, 0, v___x_4046_);
                            crate::leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
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
                            crate::leanh::lean_dec(v___x_4037_);
                            crate::leanh::lean_dec(v___x_4036_);
                            crate::leanh::lean_dec(v_h_x3f_4033_);
                            crate::leanh::lean_dec(v_body_4031_);
                            crate::leanh::lean_dec_ref(v_decls_3981_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4075_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                            v_a_4076_ = crate::leanh::lean_ctor_get(v___x_4042_, 1);
                            v_isSharedCheck_4083_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4083_ == 0 {
                                v___x_4078_ = v___x_4042_;
                                v_isShared_4079_ = v_isSharedCheck_4083_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4076_);
                                crate::leanh::lean_inc(v_a_4075_);
                                crate::leanh::lean_dec(v___x_4042_);
                                v___x_4078_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec(v___x_4036_);
                        if crate::leanh::lean_obj_tag(v___x_4084_) == 0 {
                            v_a_4085_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                            crate::leanh::lean_inc(v_a_4085_);
                            v_a_4086_ = crate::leanh::lean_ctor_get(v___x_4084_, 1);
                            crate::leanh::lean_inc(v_a_4086_);
                            crate::leanh::lean_dec_ref_known(v___x_4084_, 2);
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
                            crate::leanh::lean_dec(v___x_4037_);
                            crate::leanh::lean_dec(v_h_x3f_4033_);
                            crate::leanh::lean_dec(v_body_4031_);
                            crate::leanh::lean_dec_ref(v_decls_3981_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4087_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                            v_a_4088_ = crate::leanh::lean_ctor_get(v___x_4084_, 1);
                            v_isSharedCheck_4095_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4084_)) as u8;
                            if v_isSharedCheck_4095_ == 0 {
                                v___x_4090_ = v___x_4084_;
                                v_isShared_4091_ = v_isSharedCheck_4095_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4088_);
                                crate::leanh::lean_inc(v_a_4087_);
                                crate::leanh::lean_dec(v___x_4084_);
                                v___x_4090_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4082_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_a_4076_);
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
                    v_reuseFailAlloc_4094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_a_4088_);
                    v___x_4093_ = v_reuseFailAlloc_4094_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4093_;
            }
            12 => {
                crate::leanh::lean_inc_ref_n(v___y_4115_, 3);
                v___x_4118_ = l_Array_append___redArg(v___y_4115_, v___y_4117_);
                crate::leanh::lean_dec_ref(v___y_4117_);
                crate::leanh::lean_inc_n(v___y_4110_, 4);
                crate::leanh::lean_inc_n(v___y_4108_, 10);
                v___x_4119_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4119_, 0, v___y_4108_);
                crate::leanh::lean_ctor_set(v___x_4119_, 1, v___y_4110_);
                crate::leanh::lean_ctor_set(v___x_4119_, 2, v___x_4118_);
                v___x_4120_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4121_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4121_, 0, v___y_4108_);
                crate::leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
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
                v___x_4125_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4125_, 0, v___y_4108_);
                crate::leanh::lean_ctor_set(v___x_4125_, 1, v___x_4124_);
                crate::leanh::lean_inc_ref(v___x_4125_);
                v___x_4126_ = l_Lean_Syntax_node4(
                    v___y_4108_,
                    v___x_3940_,
                    v___y_4116_,
                    v___x_4123_,
                    v___x_4125_,
                    v___y_4112_,
                );
                v___x_4127_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4127_, 0, v___y_4108_);
                crate::leanh::lean_ctor_set(v___x_4127_, 1, v___y_4110_);
                crate::leanh::lean_ctor_set(v___x_4127_, 2, v___y_4115_);
                crate::leanh::lean_inc(v___y_4113_);
                v___x_4128_ =
                    l_Lean_Syntax_node2(v___y_4108_, v___y_4113_, v___x_4126_, v___x_4127_);
                v___x_4129_ = lean_array_push(v___y_4111_, v___x_4128_);
                v___x_4130_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4131_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4132_ = l_Array_append___redArg(v___y_4115_, v___x_4129_);
                crate::leanh::lean_dec_ref(v___x_4129_);
                v___x_4133_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4133_, 0, v___y_4108_);
                crate::leanh::lean_ctor_set(v___x_4133_, 1, v___y_4110_);
                crate::leanh::lean_ctor_set(v___x_4133_, 2, v___x_4132_);
                v___x_4134_ = l_Lean_Syntax_node1(v___y_4108_, v___x_4131_, v___x_4133_);
                v___x_4135_ =
                    l_Lean_Syntax_node2(v___y_4108_, v___x_4130_, v___x_4125_, v___x_4134_);
                v___x_4136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                crate::leanh::lean_ctor_set(v___x_4136_, 1, v___y_4109_);
                return v___x_4136_;
            }
            13 => {
                crate::leanh::lean_inc_ref_n(v___y_4144_, 3);
                v___x_4149_ = l_Array_append___redArg(v___y_4144_, v___y_4148_);
                crate::leanh::lean_dec_ref(v___y_4148_);
                crate::leanh::lean_inc_n(v___y_4141_, 4);
                crate::leanh::lean_inc_n(v___y_4145_, 10);
                v___x_4150_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4150_, 0, v___y_4145_);
                crate::leanh::lean_ctor_set(v___x_4150_, 1, v___y_4141_);
                crate::leanh::lean_ctor_set(v___x_4150_, 2, v___x_4149_);
                v___x_4151_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4152_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4152_, 0, v___y_4145_);
                crate::leanh::lean_ctor_set(v___x_4152_, 1, v___x_4151_);
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
                v___x_4156_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4156_, 0, v___y_4145_);
                crate::leanh::lean_ctor_set(v___x_4156_, 1, v___x_4155_);
                crate::leanh::lean_inc_ref(v___x_4156_);
                v___x_4157_ = l_Lean_Syntax_node4(
                    v___y_4145_,
                    v___x_3940_,
                    v___y_4143_,
                    v___x_4154_,
                    v___x_4156_,
                    v___y_4138_,
                );
                v___x_4158_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4158_, 0, v___y_4145_);
                crate::leanh::lean_ctor_set(v___x_4158_, 1, v___y_4141_);
                crate::leanh::lean_ctor_set(v___x_4158_, 2, v___y_4144_);
                crate::leanh::lean_inc(v___y_4142_);
                v___x_4159_ =
                    l_Lean_Syntax_node2(v___y_4145_, v___y_4142_, v___x_4157_, v___x_4158_);
                v___x_4160_ = lean_array_push(v___y_4146_, v___x_4159_);
                v___x_4161_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4162_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4163_ = l_Array_append___redArg(v___y_4144_, v___x_4160_);
                crate::leanh::lean_dec_ref(v___x_4160_);
                v___x_4164_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4164_, 0, v___y_4145_);
                crate::leanh::lean_ctor_set(v___x_4164_, 1, v___y_4141_);
                crate::leanh::lean_ctor_set(v___x_4164_, 2, v___x_4163_);
                v___x_4165_ = l_Lean_Syntax_node1(v___y_4145_, v___x_4162_, v___x_4164_);
                v___x_4166_ =
                    l_Lean_Syntax_node2(v___y_4145_, v___x_4161_, v___x_4156_, v___x_4165_);
                v___x_4167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4166_);
                crate::leanh::lean_ctor_set(v___x_4167_, 1, v___y_4147_);
                return v___x_4167_;
            }
            14 => {
                v___x_4178_ = lean_array_get_size(v___y_4171_);
                v___x_4179_ = l_Array_toSubarray___redArg(v___y_4171_, v___x_3945_, v___x_4178_);
                crate::leanh::lean_inc_ref(v___y_4172_);
                v___x_4180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4180_, 0, v___y_4172_);
                crate::leanh::lean_ctor_set(v___x_4180_, 1, v_body_4175_);
                v___x_4181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_4173_, v___x_4179_, v___x_4180_, v___y_4176_, v___y_4177_);
                if crate::leanh::lean_obj_tag(v___x_4181_) == 0 {
                    v_a_4182_ = crate::leanh::lean_ctor_get(v___x_4181_, 0);
                    crate::leanh::lean_inc(v_a_4182_);
                    v_a_4183_ = crate::leanh::lean_ctor_get(v___x_4181_, 1);
                    crate::leanh::lean_inc(v_a_4183_);
                    crate::leanh::lean_dec_ref_known(v___x_4181_, 2);
                    v_fst_4184_ = crate::leanh::lean_ctor_get(v_a_4182_, 0);
                    v_snd_4185_ = crate::leanh::lean_ctor_get(v_a_4182_, 1);
                    v_isSharedCheck_4204_ = (!crate::leanh::lean_is_exclusive(v_a_4182_)) as u8;
                    if v_isSharedCheck_4204_ == 0 {
                        v___x_4187_ = v_a_4182_;
                        v_isShared_4188_ = v_isSharedCheck_4204_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4185_);
                        crate::leanh::lean_inc(v_fst_4184_);
                        crate::leanh::lean_dec(v_a_4182_);
                        v___x_4187_ = crate::leanh::lean_box(0);
                        v_isShared_4188_ = v_isSharedCheck_4204_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_4174_);
                    crate::leanh::lean_dec(v___y_4170_);
                    crate::leanh::lean_dec(v___y_4169_);
                    crate::leanh::lean_dec(v_tk_3944_);
                    v_a_4205_ = crate::leanh::lean_ctor_get(v___x_4181_, 0);
                    v_a_4206_ = crate::leanh::lean_ctor_get(v___x_4181_, 1);
                    v_isSharedCheck_4213_ = (!crate::leanh::lean_is_exclusive(v___x_4181_)) as u8;
                    if v_isSharedCheck_4213_ == 0 {
                        v___x_4208_ = v___x_4181_;
                        v_isShared_4209_ = v_isSharedCheck_4213_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4206_);
                        crate::leanh::lean_inc(v_a_4205_);
                        crate::leanh::lean_dec(v___x_4181_);
                        v___x_4208_ = crate::leanh::lean_box(0);
                        v_isShared_4209_ = v_isSharedCheck_4213_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                v_ref_4189_ = crate::leanh::lean_ctor_get(v___y_4176_, 5);
                v___x_4190_ = l_Lean_SourceInfo_fromRef(v_ref_4189_, v___y_4173_);
                v___x_4191_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4192_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                crate::leanh::lean_dec(v_tk_3944_);
                v___x_4193_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4188_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4187_, 2);
                    crate::leanh::lean_ctor_set(v___x_4187_, 1, v___x_4193_);
                    crate::leanh::lean_ctor_set(v___x_4187_, 0, v___x_4192_);
                    v___x_4195_ = v___x_4187_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___x_4193_);
                    v___x_4195_ = v_reuseFailAlloc_4203_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4197_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if crate::leanh::lean_obj_tag(v___y_4170_) == 1 {
                    v_val_4198_ = crate::leanh::lean_ctor_get(v___y_4170_, 0);
                    crate::leanh::lean_inc(v_val_4198_);
                    crate::leanh::lean_dec_ref_known(v___y_4170_, 1);
                    v___x_4199_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    crate::leanh::lean_inc(v___x_4190_);
                    v___x_4200_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4200_, 0, v___x_4190_);
                    crate::leanh::lean_ctor_set(v___x_4200_, 1, v___x_4199_);
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
                    crate::leanh::lean_dec(v___y_4170_);
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
                    v_reuseFailAlloc_4212_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_a_4206_);
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
                crate::leanh::lean_dec(v___y_4219_);
                v_doElems_4225_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4226_ = l_Lean_Syntax_isIdent(v___x_4223_);
                if v___x_4226_ == 0 {
                    v___x_4227_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    crate::leanh::lean_inc(v___x_4223_);
                    v___x_4228_ = l_Lean_Syntax_isOfKind(v___x_4223_, v___x_4227_);
                    if v___x_4228_ == 0 {
                        v___x_4229_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4223_,
                                v___y_4218_,
                                v___y_4221_,
                                v___y_4222_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4229_) == 0 {
                            v_a_4230_ = crate::leanh::lean_ctor_get(v___x_4229_, 0);
                            crate::leanh::lean_inc_n(v_a_4230_, 2);
                            v_a_4231_ = crate::leanh::lean_ctor_get(v___x_4229_, 1);
                            crate::leanh::lean_inc(v_a_4231_);
                            crate::leanh::lean_dec_ref_known(v___x_4229_, 2);
                            v_ref_4232_ = crate::leanh::lean_ctor_get(v___y_4221_, 5);
                            v___x_4233_ = l_Lean_SourceInfo_fromRef(v_ref_4232_, v___y_4218_);
                            v___x_4234_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4236_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4237_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            crate::leanh::lean_inc_n(v___x_4233_, 15);
                            v___x_4239_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4239_, 0, v___x_4233_);
                            crate::leanh::lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                            v___x_4240_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4241_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4241_, 0, v___x_4233_);
                            crate::leanh::lean_ctor_set(v___x_4241_, 1, v___x_4235_);
                            crate::leanh::lean_ctor_set(v___x_4241_, 2, v___x_4240_);
                            v___x_4242_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            crate::leanh::lean_inc_ref_n(v___x_4241_, 4);
                            v___x_4243_ = l_Lean_Syntax_node2(
                                v___x_4233_,
                                v___x_4242_,
                                v___x_4241_,
                                v_a_4230_,
                            );
                            v___x_4244_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4243_);
                            v___x_4245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4246_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4246_, 0, v___x_4233_);
                            crate::leanh::lean_ctor_set(v___x_4246_, 1, v___x_4245_);
                            v___x_4247_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4248_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4250_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4250_, 0, v___x_4233_);
                            crate::leanh::lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                            v___x_4251_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4223_);
                            v___x_4252_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4251_);
                            v___x_4253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4254_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4254_, 0, v___x_4233_);
                            crate::leanh::lean_ctor_set(v___x_4254_, 1, v___x_4253_);
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
                            crate::leanh::lean_dec(v___x_4224_);
                            crate::leanh::lean_dec(v___x_4223_);
                            crate::leanh::lean_dec(v_h_x3f_4220_);
                            crate::leanh::lean_dec(v___y_4217_);
                            crate::leanh::lean_dec_ref(v___y_4216_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4262_ = crate::leanh::lean_ctor_get(v___x_4229_, 0);
                            v_a_4263_ = crate::leanh::lean_ctor_get(v___x_4229_, 1);
                            v_isSharedCheck_4270_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4229_)) as u8;
                            if v_isSharedCheck_4270_ == 0 {
                                v___x_4265_ = v___x_4229_;
                                v_isShared_4266_ = v_isSharedCheck_4270_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4263_);
                                crate::leanh::lean_inc(v_a_4262_);
                                crate::leanh::lean_dec(v___x_4229_);
                                v___x_4265_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec(v___x_4223_);
                        if crate::leanh::lean_obj_tag(v___x_4271_) == 0 {
                            v_a_4272_ = crate::leanh::lean_ctor_get(v___x_4271_, 0);
                            crate::leanh::lean_inc(v_a_4272_);
                            v_a_4273_ = crate::leanh::lean_ctor_get(v___x_4271_, 1);
                            crate::leanh::lean_inc(v_a_4273_);
                            crate::leanh::lean_dec_ref_known(v___x_4271_, 2);
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
                            crate::leanh::lean_dec(v___x_4224_);
                            crate::leanh::lean_dec(v_h_x3f_4220_);
                            crate::leanh::lean_dec(v___y_4217_);
                            crate::leanh::lean_dec_ref(v___y_4216_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4274_ = crate::leanh::lean_ctor_get(v___x_4271_, 0);
                            v_a_4275_ = crate::leanh::lean_ctor_get(v___x_4271_, 1);
                            v_isSharedCheck_4282_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4271_)) as u8;
                            if v_isSharedCheck_4282_ == 0 {
                                v___x_4277_ = v___x_4271_;
                                v_isShared_4278_ = v_isSharedCheck_4282_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4275_);
                                crate::leanh::lean_inc(v_a_4274_);
                                crate::leanh::lean_dec(v___x_4271_);
                                v___x_4277_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4269_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_a_4263_);
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
                    v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_a_4275_);
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
                crate::leanh::lean_dec(v___x_4104_);
                v___x_4287_ = l_Lean_Elab_Do_expandDoFor___closed__16;
                v___x_4288_ = l_Lean_Syntax_isOfKind(v___x_4286_, v___x_4287_);
                if v___x_4288_ == 0 {
                    v_decls_4289_ = l_Lean_Syntax_getArgs(v___x_3946_);
                    crate::leanh::lean_dec(v___x_3946_);
                    v_decls_4290_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4289_);
                    crate::leanh::lean_dec_ref(v_decls_4289_);
                    v___x_4291_ = crate::leanh::lean_box(0);
                    v___x_4292_ = lean_array_get(v___x_4291_, v_decls_4290_, v___x_3943_);
                    crate::leanh::lean_inc(v___x_4292_);
                    v___x_4293_ = l_Lean_Syntax_isOfKind(v___x_4292_, v___x_4105_);
                    if v___x_4293_ == 0 {
                        crate::leanh::lean_dec(v___x_4292_);
                        crate::leanh::lean_dec_ref(v_decls_4290_);
                        crate::leanh::lean_dec(v_tk_3944_);
                        crate::leanh::lean_dec(v_stx_3937_);
                        v___x_4294_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                        return v___x_4294_;
                    } else {
                        v___x_4295_ = crate::leanh::lean_unsigned_to_nat(3);
                        v_body_4296_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4295_);
                        crate::leanh::lean_dec(v_stx_3937_);
                        v___x_4297_ = l_Lean_Syntax_getArg(v___x_4292_, v___x_3943_);
                        v___x_4298_ = l_Lean_Syntax_isNone(v___x_4297_);
                        if v___x_4298_ == 0 {
                            v___x_4299_ = crate::leanh::lean_unsigned_to_nat(2);
                            crate::leanh::lean_inc(v___x_4297_);
                            v___x_4300_ = l_Lean_Syntax_matchesNull(v___x_4297_, v___x_4299_);
                            if v___x_4300_ == 0 {
                                crate::leanh::lean_dec(v___x_4297_);
                                crate::leanh::lean_dec(v_body_4296_);
                                crate::leanh::lean_dec(v___x_4292_);
                                crate::leanh::lean_dec_ref(v_decls_4290_);
                                crate::leanh::lean_dec(v_tk_3944_);
                                v___x_4301_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                                return v___x_4301_;
                            } else {
                                v_h_x3f_4302_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_3943_);
                                crate::leanh::lean_dec(v___x_4297_);
                                v___x_4303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4303_, 0, v_h_x3f_4302_);
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
                            crate::leanh::lean_dec(v___x_4297_);
                            v___x_4304_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v___x_3946_);
                    crate::leanh::lean_dec(v_tk_3944_);
                    crate::leanh::lean_dec(v_stx_3937_);
                    v___x_4305_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                    return v___x_4305_;
                }
            }
            25 => {
                crate::leanh::lean_inc_ref_n(v___y_4311_, 3);
                v___x_4318_ = l_Array_append___redArg(v___y_4311_, v___y_4317_);
                crate::leanh::lean_dec_ref(v___y_4317_);
                crate::leanh::lean_inc_n(v___y_4307_, 4);
                crate::leanh::lean_inc_n(v___y_4308_, 10);
                v___x_4319_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4319_, 0, v___y_4308_);
                crate::leanh::lean_ctor_set(v___x_4319_, 1, v___y_4307_);
                crate::leanh::lean_ctor_set(v___x_4319_, 2, v___x_4318_);
                v___x_4320_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4321_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4321_, 0, v___y_4308_);
                crate::leanh::lean_ctor_set(v___x_4321_, 1, v___x_4320_);
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
                v___x_4325_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4325_, 0, v___y_4308_);
                crate::leanh::lean_ctor_set(v___x_4325_, 1, v___x_4324_);
                crate::leanh::lean_inc_ref(v___x_4325_);
                v___x_4326_ = l_Lean_Syntax_node4(
                    v___y_4308_,
                    v___x_3940_,
                    v___y_4312_,
                    v___x_4323_,
                    v___x_4325_,
                    v___y_4310_,
                );
                v___x_4327_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4327_, 0, v___y_4308_);
                crate::leanh::lean_ctor_set(v___x_4327_, 1, v___y_4307_);
                crate::leanh::lean_ctor_set(v___x_4327_, 2, v___y_4311_);
                crate::leanh::lean_inc(v___y_4313_);
                v___x_4328_ =
                    l_Lean_Syntax_node2(v___y_4308_, v___y_4313_, v___x_4326_, v___x_4327_);
                v___x_4329_ = lean_array_push(v___y_4309_, v___x_4328_);
                v___x_4330_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4331_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4332_ = l_Array_append___redArg(v___y_4311_, v___x_4329_);
                crate::leanh::lean_dec_ref(v___x_4329_);
                v___x_4333_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4333_, 0, v___y_4308_);
                crate::leanh::lean_ctor_set(v___x_4333_, 1, v___y_4307_);
                crate::leanh::lean_ctor_set(v___x_4333_, 2, v___x_4332_);
                v___x_4334_ = l_Lean_Syntax_node1(v___y_4308_, v___x_4331_, v___x_4333_);
                v___x_4335_ =
                    l_Lean_Syntax_node2(v___y_4308_, v___x_4330_, v___x_4325_, v___x_4334_);
                v___x_4336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4336_, 0, v___x_4335_);
                crate::leanh::lean_ctor_set(v___x_4336_, 1, v___y_4316_);
                return v___x_4336_;
            }
            26 => {
                v___x_4348_ = lean_array_get_size(v_decls_4339_);
                v___x_4349_ = l_Array_toSubarray___redArg(v_decls_4339_, v___x_3945_, v___x_4348_);
                crate::leanh::lean_inc_ref(v___y_4343_);
                v___x_4350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4350_, 0, v___y_4343_);
                crate::leanh::lean_ctor_set(v___x_4350_, 1, v_body_4345_);
                v___x_4351_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_4337_, v___x_4349_, v___x_4350_, v___y_4346_, v___y_4347_);
                if crate::leanh::lean_obj_tag(v___x_4351_) == 0 {
                    v_a_4352_ = crate::leanh::lean_ctor_get(v___x_4351_, 0);
                    crate::leanh::lean_inc(v_a_4352_);
                    v_a_4353_ = crate::leanh::lean_ctor_get(v___x_4351_, 1);
                    crate::leanh::lean_inc(v_a_4353_);
                    crate::leanh::lean_dec_ref_known(v___x_4351_, 2);
                    v_fst_4354_ = crate::leanh::lean_ctor_get(v_a_4352_, 0);
                    v_snd_4355_ = crate::leanh::lean_ctor_get(v_a_4352_, 1);
                    v_isSharedCheck_4374_ = (!crate::leanh::lean_is_exclusive(v_a_4352_)) as u8;
                    if v_isSharedCheck_4374_ == 0 {
                        v___x_4357_ = v_a_4352_;
                        v_isShared_4358_ = v_isSharedCheck_4374_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4355_);
                        crate::leanh::lean_inc(v_fst_4354_);
                        crate::leanh::lean_dec(v_a_4352_);
                        v___x_4357_ = crate::leanh::lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4374_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_4344_);
                    crate::leanh::lean_dec(v___y_4342_);
                    crate::leanh::lean_dec(v___y_4341_);
                    crate::leanh::lean_dec(v_tk_3944_);
                    v_a_4375_ = crate::leanh::lean_ctor_get(v___x_4351_, 0);
                    v_a_4376_ = crate::leanh::lean_ctor_get(v___x_4351_, 1);
                    v_isSharedCheck_4383_ = (!crate::leanh::lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4378_ = v___x_4351_;
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4376_);
                        crate::leanh::lean_inc(v_a_4375_);
                        crate::leanh::lean_dec(v___x_4351_);
                        v___x_4378_ = crate::leanh::lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                v_ref_4359_ = crate::leanh::lean_ctor_get(v___y_4346_, 5);
                v___x_4360_ = l_Lean_SourceInfo_fromRef(v_ref_4359_, v___x_4337_);
                v___x_4361_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4362_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                crate::leanh::lean_dec(v_tk_3944_);
                v___x_4363_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4358_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4357_, 2);
                    crate::leanh::lean_ctor_set(v___x_4357_, 1, v___x_4363_);
                    crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4362_);
                    v___x_4365_ = v___x_4357_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 1, v___x_4363_);
                    v___x_4365_ = v_reuseFailAlloc_4373_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4367_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if crate::leanh::lean_obj_tag(v___y_4341_) == 1 {
                    v_val_4368_ = crate::leanh::lean_ctor_get(v___y_4341_, 0);
                    crate::leanh::lean_inc(v_val_4368_);
                    crate::leanh::lean_dec_ref_known(v___y_4341_, 1);
                    v___x_4369_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    crate::leanh::lean_inc(v___x_4360_);
                    v___x_4370_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4370_, 0, v___x_4360_);
                    crate::leanh::lean_ctor_set(v___x_4370_, 1, v___x_4369_);
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
                    crate::leanh::lean_dec(v___y_4341_);
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
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_a_4376_);
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
                crate::leanh::lean_dec(v___x_4385_);
                v_doElems_4396_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4397_ = l_Lean_Syntax_isIdent(v___x_4394_);
                if v___x_4397_ == 0 {
                    v___x_4398_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    crate::leanh::lean_inc(v___x_4394_);
                    v___x_4399_ = l_Lean_Syntax_isOfKind(v___x_4394_, v___x_4398_);
                    if v___x_4399_ == 0 {
                        v___x_4400_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4394_,
                                v___x_4399_,
                                v___y_4392_,
                                v___y_4393_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4400_) == 0 {
                            v_a_4401_ = crate::leanh::lean_ctor_get(v___x_4400_, 0);
                            crate::leanh::lean_inc_n(v_a_4401_, 2);
                            v_a_4402_ = crate::leanh::lean_ctor_get(v___x_4400_, 1);
                            crate::leanh::lean_inc(v_a_4402_);
                            crate::leanh::lean_dec_ref_known(v___x_4400_, 2);
                            v_ref_4403_ = crate::leanh::lean_ctor_get(v___y_4392_, 5);
                            v___x_4404_ = l_Lean_SourceInfo_fromRef(v_ref_4403_, v___x_4399_);
                            v___x_4405_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4407_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4408_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4409_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            crate::leanh::lean_inc_n(v___x_4404_, 15);
                            v___x_4410_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4410_, 0, v___x_4404_);
                            crate::leanh::lean_ctor_set(v___x_4410_, 1, v___x_4409_);
                            v___x_4411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4412_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4412_, 0, v___x_4404_);
                            crate::leanh::lean_ctor_set(v___x_4412_, 1, v___x_4406_);
                            crate::leanh::lean_ctor_set(v___x_4412_, 2, v___x_4411_);
                            v___x_4413_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            crate::leanh::lean_inc_ref_n(v___x_4412_, 4);
                            v___x_4414_ = l_Lean_Syntax_node2(
                                v___x_4404_,
                                v___x_4413_,
                                v___x_4412_,
                                v_a_4401_,
                            );
                            v___x_4415_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4414_);
                            v___x_4416_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4417_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4417_, 0, v___x_4404_);
                            crate::leanh::lean_ctor_set(v___x_4417_, 1, v___x_4416_);
                            v___x_4418_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4419_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4421_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4404_);
                            crate::leanh::lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                            v___x_4422_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4394_);
                            v___x_4423_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4422_);
                            v___x_4424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4425_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4425_, 0, v___x_4404_);
                            crate::leanh::lean_ctor_set(v___x_4425_, 1, v___x_4424_);
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
                            crate::leanh::lean_dec(v___x_4395_);
                            crate::leanh::lean_dec(v___x_4394_);
                            crate::leanh::lean_dec(v_h_x3f_4391_);
                            crate::leanh::lean_dec(v_body_4389_);
                            crate::leanh::lean_dec_ref(v_decls_4339_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4433_ = crate::leanh::lean_ctor_get(v___x_4400_, 0);
                            v_a_4434_ = crate::leanh::lean_ctor_get(v___x_4400_, 1);
                            v_isSharedCheck_4441_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4400_)) as u8;
                            if v_isSharedCheck_4441_ == 0 {
                                v___x_4436_ = v___x_4400_;
                                v_isShared_4437_ = v_isSharedCheck_4441_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4434_);
                                crate::leanh::lean_inc(v_a_4433_);
                                crate::leanh::lean_dec(v___x_4400_);
                                v___x_4436_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec(v___x_4394_);
                        if crate::leanh::lean_obj_tag(v___x_4442_) == 0 {
                            v_a_4443_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                            crate::leanh::lean_inc(v_a_4443_);
                            v_a_4444_ = crate::leanh::lean_ctor_get(v___x_4442_, 1);
                            crate::leanh::lean_inc(v_a_4444_);
                            crate::leanh::lean_dec_ref_known(v___x_4442_, 2);
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
                            crate::leanh::lean_dec(v___x_4395_);
                            crate::leanh::lean_dec(v_h_x3f_4391_);
                            crate::leanh::lean_dec(v_body_4389_);
                            crate::leanh::lean_dec_ref(v_decls_4339_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4445_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                            v_a_4446_ = crate::leanh::lean_ctor_get(v___x_4442_, 1);
                            v_isSharedCheck_4453_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4442_)) as u8;
                            if v_isSharedCheck_4453_ == 0 {
                                v___x_4448_ = v___x_4442_;
                                v_isShared_4449_ = v_isSharedCheck_4453_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4446_);
                                crate::leanh::lean_inc(v_a_4445_);
                                crate::leanh::lean_dec(v___x_4442_);
                                v___x_4448_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4440_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_a_4434_);
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
                    v_reuseFailAlloc_4452_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_a_4446_);
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
                crate::leanh::lean_inc_ref(v___y_4471_);
                v___x_4478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4478_, 0, v___y_4471_);
                crate::leanh::lean_ctor_set(v___x_4478_, 1, v_body_4473_);
                v___x_4479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_4465_, v___x_4477_, v___x_4478_, v___y_4474_, v___y_4475_);
                if crate::leanh::lean_obj_tag(v___x_4479_) == 0 {
                    v_a_4480_ = crate::leanh::lean_ctor_get(v___x_4479_, 0);
                    crate::leanh::lean_inc(v_a_4480_);
                    v_a_4481_ = crate::leanh::lean_ctor_get(v___x_4479_, 1);
                    crate::leanh::lean_inc(v_a_4481_);
                    crate::leanh::lean_dec_ref_known(v___x_4479_, 2);
                    v_fst_4482_ = crate::leanh::lean_ctor_get(v_a_4480_, 0);
                    v_snd_4483_ = crate::leanh::lean_ctor_get(v_a_4480_, 1);
                    v_isSharedCheck_4502_ = (!crate::leanh::lean_is_exclusive(v_a_4480_)) as u8;
                    if v_isSharedCheck_4502_ == 0 {
                        v___x_4485_ = v_a_4480_;
                        v_isShared_4486_ = v_isSharedCheck_4502_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4483_);
                        crate::leanh::lean_inc(v_fst_4482_);
                        crate::leanh::lean_dec(v_a_4480_);
                        v___x_4485_ = crate::leanh::lean_box(0);
                        v_isShared_4486_ = v_isSharedCheck_4502_;
                        state = 37;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_4472_);
                    crate::leanh::lean_dec(v___y_4470_);
                    crate::leanh::lean_dec(v___y_4469_);
                    crate::leanh::lean_dec(v_tk_3944_);
                    v_a_4503_ = crate::leanh::lean_ctor_get(v___x_4479_, 0);
                    v_a_4504_ = crate::leanh::lean_ctor_get(v___x_4479_, 1);
                    v_isSharedCheck_4511_ = (!crate::leanh::lean_is_exclusive(v___x_4479_)) as u8;
                    if v_isSharedCheck_4511_ == 0 {
                        v___x_4506_ = v___x_4479_;
                        v_isShared_4507_ = v_isSharedCheck_4511_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4504_);
                        crate::leanh::lean_inc(v_a_4503_);
                        crate::leanh::lean_dec(v___x_4479_);
                        v___x_4506_ = crate::leanh::lean_box(0);
                        v_isShared_4507_ = v_isSharedCheck_4511_;
                        state = 39;
                        continue;
                    }
                }
            }
            37 => {
                v_ref_4487_ = crate::leanh::lean_ctor_get(v___y_4474_, 5);
                v___x_4488_ = l_Lean_SourceInfo_fromRef(v_ref_4487_, v___x_4465_);
                v___x_4489_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4490_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                crate::leanh::lean_dec(v_tk_3944_);
                v___x_4491_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4486_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4485_, 2);
                    crate::leanh::lean_ctor_set(v___x_4485_, 1, v___x_4491_);
                    crate::leanh::lean_ctor_set(v___x_4485_, 0, v___x_4490_);
                    v___x_4493_ = v___x_4485_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4491_);
                    v___x_4493_ = v_reuseFailAlloc_4501_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_4494_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4495_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if crate::leanh::lean_obj_tag(v___y_4470_) == 1 {
                    v_val_4496_ = crate::leanh::lean_ctor_get(v___y_4470_, 0);
                    crate::leanh::lean_inc(v_val_4496_);
                    crate::leanh::lean_dec_ref_known(v___y_4470_, 1);
                    v___x_4497_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    crate::leanh::lean_inc(v___x_4488_);
                    v___x_4498_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4498_, 0, v___x_4488_);
                    crate::leanh::lean_ctor_set(v___x_4498_, 1, v___x_4497_);
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
                    crate::leanh::lean_dec(v___y_4470_);
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
                    v_reuseFailAlloc_4510_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_a_4504_);
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
                crate::leanh::lean_dec(v___x_4513_);
                v_doElems_4524_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4525_ = l_Lean_Syntax_isIdent(v___x_4522_);
                if v___x_4525_ == 0 {
                    v___x_4526_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    crate::leanh::lean_inc(v___x_4522_);
                    v___x_4527_ = l_Lean_Syntax_isOfKind(v___x_4522_, v___x_4526_);
                    if v___x_4527_ == 0 {
                        v___x_4528_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4522_,
                                v___x_4527_,
                                v___y_4520_,
                                v___y_4521_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4528_) == 0 {
                            v_a_4529_ = crate::leanh::lean_ctor_get(v___x_4528_, 0);
                            crate::leanh::lean_inc_n(v_a_4529_, 2);
                            v_a_4530_ = crate::leanh::lean_ctor_get(v___x_4528_, 1);
                            crate::leanh::lean_inc(v_a_4530_);
                            crate::leanh::lean_dec_ref_known(v___x_4528_, 2);
                            v_ref_4531_ = crate::leanh::lean_ctor_get(v___y_4520_, 5);
                            v___x_4532_ = l_Lean_SourceInfo_fromRef(v_ref_4531_, v___x_4527_);
                            v___x_4533_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4535_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4536_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4537_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            crate::leanh::lean_inc_n(v___x_4532_, 15);
                            v___x_4538_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4538_, 0, v___x_4532_);
                            crate::leanh::lean_ctor_set(v___x_4538_, 1, v___x_4537_);
                            v___x_4539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4540_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4540_, 0, v___x_4532_);
                            crate::leanh::lean_ctor_set(v___x_4540_, 1, v___x_4534_);
                            crate::leanh::lean_ctor_set(v___x_4540_, 2, v___x_4539_);
                            v___x_4541_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            crate::leanh::lean_inc_ref_n(v___x_4540_, 4);
                            v___x_4542_ = l_Lean_Syntax_node2(
                                v___x_4532_,
                                v___x_4541_,
                                v___x_4540_,
                                v_a_4529_,
                            );
                            v___x_4543_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4542_);
                            v___x_4544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4545_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4545_, 0, v___x_4532_);
                            crate::leanh::lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                            v___x_4546_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4547_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4549_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4549_, 0, v___x_4532_);
                            crate::leanh::lean_ctor_set(v___x_4549_, 1, v___x_4548_);
                            v___x_4550_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4522_);
                            v___x_4551_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4550_);
                            v___x_4552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4553_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4553_, 0, v___x_4532_);
                            crate::leanh::lean_ctor_set(v___x_4553_, 1, v___x_4552_);
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
                            crate::leanh::lean_dec(v___x_4523_);
                            crate::leanh::lean_dec(v___x_4522_);
                            crate::leanh::lean_dec(v_h_x3f_4519_);
                            crate::leanh::lean_dec(v_body_4517_);
                            crate::leanh::lean_dec_ref(v_decls_4467_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4561_ = crate::leanh::lean_ctor_get(v___x_4528_, 0);
                            v_a_4562_ = crate::leanh::lean_ctor_get(v___x_4528_, 1);
                            v_isSharedCheck_4569_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4528_)) as u8;
                            if v_isSharedCheck_4569_ == 0 {
                                v___x_4564_ = v___x_4528_;
                                v_isShared_4565_ = v_isSharedCheck_4569_;
                                state = 42;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4562_);
                                crate::leanh::lean_inc(v_a_4561_);
                                crate::leanh::lean_dec(v___x_4528_);
                                v___x_4564_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec(v___x_4522_);
                        if crate::leanh::lean_obj_tag(v___x_4570_) == 0 {
                            v_a_4571_ = crate::leanh::lean_ctor_get(v___x_4570_, 0);
                            crate::leanh::lean_inc(v_a_4571_);
                            v_a_4572_ = crate::leanh::lean_ctor_get(v___x_4570_, 1);
                            crate::leanh::lean_inc(v_a_4572_);
                            crate::leanh::lean_dec_ref_known(v___x_4570_, 2);
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
                            crate::leanh::lean_dec(v___x_4523_);
                            crate::leanh::lean_dec(v_h_x3f_4519_);
                            crate::leanh::lean_dec(v_body_4517_);
                            crate::leanh::lean_dec_ref(v_decls_4467_);
                            crate::leanh::lean_dec(v_tk_3944_);
                            v_a_4573_ = crate::leanh::lean_ctor_get(v___x_4570_, 0);
                            v_a_4574_ = crate::leanh::lean_ctor_get(v___x_4570_, 1);
                            v_isSharedCheck_4581_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4570_)) as u8;
                            if v_isSharedCheck_4581_ == 0 {
                                v___x_4576_ = v___x_4570_;
                                v_isShared_4577_ = v_isSharedCheck_4581_;
                                state = 44;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4574_);
                                crate::leanh::lean_inc(v_a_4573_);
                                crate::leanh::lean_dec(v___x_4570_);
                                v___x_4576_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4568_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 1, v_a_4562_);
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
                    v_reuseFailAlloc_4580_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_a_4574_);
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
    mut v_stx_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Lean_Elab_Do_expandDoFor(v_stx_4589_, v_a_4590_, v_a_4591_);
    crate::leanh::lean_dec_ref(v_a_4590_);
    return v_res_4592_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(
    mut v___x_4593_: u8,
    mut v_inst_4594_: *mut crate::leanh::LeanObject,
    mut v_R_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_b_4597_: *mut crate::leanh::LeanObject,
    mut v_c_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_4602_: *mut crate::leanh::LeanObject,
    mut v_inst_4603_: *mut crate::leanh::LeanObject,
    mut v_R_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_b_4606_: *mut crate::leanh::LeanObject,
    mut v_c_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_148624__boxed_4610_: u8 = 0;
    let mut v_res_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_148624__boxed_4610_ = (crate::leanh::lean_unbox(v___x_4602_) as u8);
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
    crate::leanh::lean_dec_ref(v___y_4608_);
    return v_res_4611_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Lean_Elab_macroAttribute;
    v___x_4620_ = l_Lean_Elab_Do_expandDoFor___closed__1;
    v___x_4621_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1;
    v___x_4622_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_4624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4625_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
    return v_res_4625_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = crate::leanh::lean_box(0);
    v___x_4627_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4628_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    crate::leanh::lean_ctor_set(v___x_4628_, 1, v___x_4626_);
    return v___x_4628_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
    v___x_4631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4631_, 0, v___x_4630_);
    return v___x_4631_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(
    mut v___y_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
    return v_res_4633_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(
    mut v_00_u03b1_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
    return v___x_4643_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(
    mut v_00_u03b1_4644_: *mut crate::leanh::LeanObject,
    mut v___y_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4650_);
    crate::leanh::lean_dec(v___y_4649_);
    crate::leanh::lean_dec_ref(v___y_4648_);
    crate::leanh::lean_dec(v___y_4647_);
    crate::leanh::lean_dec_ref(v___y_4646_);
    crate::leanh::lean_dec_ref(v___y_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(
    mut v_k_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v_b_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4662_);
    crate::leanh::lean_inc_ref(v___y_4661_);
    crate::leanh::lean_inc(v___y_4660_);
    crate::leanh::lean_inc_ref(v___y_4659_);
    crate::leanh::lean_inc(v___y_4657_);
    crate::leanh::lean_inc_ref(v___y_4656_);
    crate::leanh::lean_inc_ref(v___y_4655_);
    v___x_4664_ = crate::leanh::lean_apply_9(
        v_k_4654_,
        v_b_4658_,
        v___y_4655_,
        v___y_4656_,
        v___y_4657_,
        v___y_4659_,
        v___y_4660_,
        v___y_4661_,
        v___y_4662_,
        crate::leanh::lean_box(0),
    );
    return v___x_4664_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(
    mut v_k_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
    mut v_b_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4673_);
    crate::leanh::lean_dec_ref(v___y_4672_);
    crate::leanh::lean_dec(v___y_4671_);
    crate::leanh::lean_dec_ref(v___y_4670_);
    crate::leanh::lean_dec(v___y_4668_);
    crate::leanh::lean_dec_ref(v___y_4667_);
    crate::leanh::lean_dec_ref(v___y_4666_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
    mut v_name_4676_: *mut crate::leanh::LeanObject,
    mut v_bi_4677_: u8,
    mut v_type_4678_: *mut crate::leanh::LeanObject,
    mut v_k_4679_: *mut crate::leanh::LeanObject,
    mut v_kind_4680_: u8,
    mut v___y_4681_: *mut crate::leanh::LeanObject,
    mut v___y_4682_: *mut crate::leanh::LeanObject,
    mut v___y_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4683_);
                crate::leanh::lean_inc_ref(v___y_4682_);
                crate::leanh::lean_inc_ref(v___y_4681_);
                v___f_4689_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                crate::leanh::lean_closure_set(v___f_4689_, 0, v_k_4679_);
                crate::leanh::lean_closure_set(v___f_4689_, 1, v___y_4681_);
                crate::leanh::lean_closure_set(v___f_4689_, 2, v___y_4682_);
                crate::leanh::lean_closure_set(v___f_4689_, 3, v___y_4683_);
                v___x_4690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
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
                if crate::leanh::lean_obj_tag(v___x_4690_) == 0 {
                    return v___x_4690_;
                } else {
                    v_a_4691_ = crate::leanh::lean_ctor_get(v___x_4690_, 0);
                    v_isSharedCheck_4698_ = (!crate::leanh::lean_is_exclusive(v___x_4690_)) as u8;
                    if v_isSharedCheck_4698_ == 0 {
                        v___x_4693_ = v___x_4690_;
                        v_isShared_4694_ = v_isSharedCheck_4698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4691_);
                        crate::leanh::lean_dec(v___x_4690_);
                        v___x_4693_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4697_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
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
    mut v_name_4699_: *mut crate::leanh::LeanObject,
    mut v_bi_4700_: *mut crate::leanh::LeanObject,
    mut v_type_4701_: *mut crate::leanh::LeanObject,
    mut v_k_4702_: *mut crate::leanh::LeanObject,
    mut v_kind_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4712_: u8 = 0;
    let mut v_kind_boxed_4713_: u8 = 0;
    let mut v_res_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4712_ = (crate::leanh::lean_unbox(v_bi_4700_) as u8);
    v_kind_boxed_4713_ = (crate::leanh::lean_unbox(v_kind_4703_) as u8);
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
    crate::leanh::lean_dec(v___y_4710_);
    crate::leanh::lean_dec_ref(v___y_4709_);
    crate::leanh::lean_dec(v___y_4708_);
    crate::leanh::lean_dec_ref(v___y_4707_);
    crate::leanh::lean_dec(v___y_4706_);
    crate::leanh::lean_dec_ref(v___y_4705_);
    crate::leanh::lean_dec_ref(v___y_4704_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(
    mut v_00_u03b1_4715_: *mut crate::leanh::LeanObject,
    mut v_name_4716_: *mut crate::leanh::LeanObject,
    mut v_bi_4717_: u8,
    mut v_type_4718_: *mut crate::leanh::LeanObject,
    mut v_k_4719_: *mut crate::leanh::LeanObject,
    mut v_kind_4720_: u8,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4730_: *mut crate::leanh::LeanObject,
    mut v_name_4731_: *mut crate::leanh::LeanObject,
    mut v_bi_4732_: *mut crate::leanh::LeanObject,
    mut v_type_4733_: *mut crate::leanh::LeanObject,
    mut v_k_4734_: *mut crate::leanh::LeanObject,
    mut v_kind_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4744_: u8 = 0;
    let mut v_kind_boxed_4745_: u8 = 0;
    let mut v_res_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4744_ = (crate::leanh::lean_unbox(v_bi_4732_) as u8);
    v_kind_boxed_4745_ = (crate::leanh::lean_unbox(v_kind_4735_) as u8);
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
    crate::leanh::lean_dec(v___y_4742_);
    crate::leanh::lean_dec_ref(v___y_4741_);
    crate::leanh::lean_dec(v___y_4740_);
    crate::leanh::lean_dec_ref(v___y_4739_);
    crate::leanh::lean_dec(v___y_4738_);
    crate::leanh::lean_dec_ref(v___y_4737_);
    crate::leanh::lean_dec_ref(v___y_4736_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__0(
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_x_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
    mut v___y_4752_: *mut crate::leanh::LeanObject,
    mut v___y_4753_: *mut crate::leanh::LeanObject,
    mut v___y_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4757_, 0, v_a_4747_);
    return v___x_4757_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__0___boxed(
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_x_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
    mut v___y_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
    mut v___y_4767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4766_);
    crate::leanh::lean_dec_ref(v___y_4765_);
    crate::leanh::lean_dec(v___y_4764_);
    crate::leanh::lean_dec_ref(v___y_4763_);
    crate::leanh::lean_dec(v___y_4762_);
    crate::leanh::lean_dec_ref(v___y_4761_);
    crate::leanh::lean_dec_ref(v___y_4760_);
    crate::leanh::lean_dec_ref(v_x_4759_);
    return v_res_4768_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__2(
    mut v_x_4769_: *mut crate::leanh::LeanObject,
    mut v___f_4770_: *mut crate::leanh::LeanObject,
    mut v___x_4771_: *mut crate::leanh::LeanObject,
    mut v_x_4772_: *mut crate::leanh::LeanObject,
    mut v_x_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4774_ = l_Lean_TSyntax_getId(v_x_4769_);
    v___x_4775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4775_, 0, v___x_4774_);
    crate::leanh::lean_ctor_set(v___x_4775_, 1, v___f_4770_);
    v___x_4776_ = lean_mk_empty_array_with_capacity(v___x_4771_);
    v___x_4777_ = lean_array_push(v___x_4776_, v___x_4775_);
    return v___x_4777_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__2___boxed(
    mut v_x_4778_: *mut crate::leanh::LeanObject,
    mut v___f_4779_: *mut crate::leanh::LeanObject,
    mut v___x_4780_: *mut crate::leanh::LeanObject,
    mut v_x_4781_: *mut crate::leanh::LeanObject,
    mut v_x_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_Elab_Do_elabDoFor___lam__2(
        v_x_4778_,
        v___f_4779_,
        v___x_4780_,
        v_x_4781_,
        v_x_4782_,
    );
    crate::leanh::lean_dec(v_x_4782_);
    crate::leanh::lean_dec(v_x_4781_);
    crate::leanh::lean_dec(v___x_4780_);
    crate::leanh::lean_dec(v_x_4778_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__1(
    mut v_a_4784_: *mut crate::leanh::LeanObject,
    mut v___x_4785_: *mut crate::leanh::LeanObject,
    mut v___x_4786_: u8,
    mut v_r_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_4796_ = crate::leanh::lean_ctor_get(v_a_4784_, 1);
    crate::leanh::lean_inc_ref(v_k_4796_);
    crate::leanh::lean_dec_ref(v_a_4784_);
    crate::leanh::lean_inc(v___y_4794_);
    crate::leanh::lean_inc_ref(v___y_4793_);
    crate::leanh::lean_inc(v___y_4792_);
    crate::leanh::lean_inc_ref(v___y_4791_);
    crate::leanh::lean_inc(v___y_4790_);
    crate::leanh::lean_inc_ref(v___y_4789_);
    crate::leanh::lean_inc_ref(v___y_4788_);
    crate::leanh::lean_inc_ref(v_r_4787_);
    v___x_4797_ = crate::leanh::lean_apply_9(
        v_k_4796_,
        v_r_4787_,
        v___y_4788_,
        v___y_4789_,
        v___y_4790_,
        v___y_4791_,
        v___y_4792_,
        v___y_4793_,
        v___y_4794_,
        crate::leanh::lean_box(0),
    );
    if crate::leanh::lean_obj_tag(v___x_4797_) == 0 {
        let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4801_: u8 = 0;
        let mut v___x_4802_: u8 = 0;
        let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
        crate::leanh::lean_inc(v_a_4798_);
        crate::leanh::lean_dec_ref_known(v___x_4797_, 1);
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
        crate::leanh::lean_dec_ref(v___x_4800_);
        return v___x_4803_;
    } else {
        crate::leanh::lean_dec_ref(v_r_4787_);
        return v___x_4797_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__1___boxed(
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v___x_4805_: *mut crate::leanh::LeanObject,
    mut v___x_4806_: *mut crate::leanh::LeanObject,
    mut v_r_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
    mut v___y_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_71074__boxed_4816_: u8 = 0;
    let mut v_res_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_71074__boxed_4816_ = (crate::leanh::lean_unbox(v___x_4806_) as u8);
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
    crate::leanh::lean_dec(v___y_4814_);
    crate::leanh::lean_dec_ref(v___y_4813_);
    crate::leanh::lean_dec(v___y_4812_);
    crate::leanh::lean_dec_ref(v___y_4811_);
    crate::leanh::lean_dec(v___y_4810_);
    crate::leanh::lean_dec_ref(v___y_4809_);
    crate::leanh::lean_dec_ref(v___y_4808_);
    crate::leanh::lean_dec(v___x_4805_);
    return v_res_4817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(
    mut v___x_4818_: *mut crate::leanh::LeanObject,
    mut v_as_4819_: *mut crate::leanh::LeanObject,
    mut v_sz_4820_: usize,
    mut v_i_4821_: usize,
    mut v_b_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: u8 = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v_a_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut v_a_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4861_: u8 = 0;
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_a_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4873_: u8 = 0;
    let mut v_a_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4877_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4830_ = lean_usize_dec_lt(v_i_4821_, v_sz_4820_);
                if v___x_4830_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4818_);
                    v___x_4831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4831_, 0, v_b_4822_);
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
                    if crate::leanh::lean_obj_tag(v___x_4834_) == 0 {
                        v_a_4835_ = crate::leanh::lean_ctor_get(v___x_4834_, 0);
                        crate::leanh::lean_inc_n(v_a_4835_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4834_, 1);
                        v___x_4836_ = l_Lean_LocalDecl_toExpr(v_a_4835_);
                        v___x_4837_ = crate::leanh::lean_box(0);
                        v___x_4838_ = crate::leanh::lean_box(0);
                        v___x_4839_ = 0;
                        crate::leanh::lean_inc_ref(v___x_4836_);
                        crate::leanh::lean_inc(v_a_4832_);
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
                        if crate::leanh::lean_obj_tag(v___x_4840_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4840_, 1);
                            v___x_4841_ = l_Lean_LocalDecl_type(v_a_4835_);
                            crate::leanh::lean_dec(v_a_4835_);
                            v___x_4842_ = l_Lean_Meta_getDecLevel(
                                v___x_4841_,
                                v___y_4825_,
                                v___y_4826_,
                                v___y_4827_,
                                v___y_4828_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4842_) == 0 {
                                v_a_4843_ = crate::leanh::lean_ctor_get(v___x_4842_, 0);
                                crate::leanh::lean_inc(v_a_4843_);
                                crate::leanh::lean_dec_ref_known(v___x_4842_, 1);
                                v_u_4844_ = crate::leanh::lean_ctor_get(v___x_4818_, 1);
                                crate::leanh::lean_inc(v_u_4844_);
                                v___x_4845_ = l_Lean_Meta_isLevelDefEq(
                                    v_a_4843_,
                                    v_u_4844_,
                                    v___y_4825_,
                                    v___y_4826_,
                                    v___y_4827_,
                                    v___y_4828_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4845_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4845_, 1);
                                    v___x_4846_ = lean_array_push(v_b_4822_, v___x_4836_);
                                    v___x_4847_ = 1usize;
                                    v___x_4848_ = lean_usize_add(v_i_4821_, v___x_4847_);
                                    v_i_4821_ = v___x_4848_;
                                    v_b_4822_ = v___x_4846_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4836_);
                                    crate::leanh::lean_dec_ref(v_b_4822_);
                                    crate::leanh::lean_dec_ref(v___x_4818_);
                                    v_a_4850_ = crate::leanh::lean_ctor_get(v___x_4845_, 0);
                                    v_isSharedCheck_4857_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4845_)) as u8;
                                    if v_isSharedCheck_4857_ == 0 {
                                        v___x_4852_ = v___x_4845_;
                                        v_isShared_4853_ = v_isSharedCheck_4857_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4850_);
                                        crate::leanh::lean_dec(v___x_4845_);
                                        v___x_4852_ = crate::leanh::lean_box(0);
                                        v_isShared_4853_ = v_isSharedCheck_4857_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4836_);
                                crate::leanh::lean_dec_ref(v_b_4822_);
                                crate::leanh::lean_dec_ref(v___x_4818_);
                                v_a_4858_ = crate::leanh::lean_ctor_get(v___x_4842_, 0);
                                v_isSharedCheck_4865_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4842_)) as u8;
                                if v_isSharedCheck_4865_ == 0 {
                                    v___x_4860_ = v___x_4842_;
                                    v_isShared_4861_ = v_isSharedCheck_4865_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4858_);
                                    crate::leanh::lean_dec(v___x_4842_);
                                    v___x_4860_ = crate::leanh::lean_box(0);
                                    v_isShared_4861_ = v_isSharedCheck_4865_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4836_);
                            crate::leanh::lean_dec(v_a_4835_);
                            crate::leanh::lean_dec_ref(v_b_4822_);
                            crate::leanh::lean_dec_ref(v___x_4818_);
                            v_a_4866_ = crate::leanh::lean_ctor_get(v___x_4840_, 0);
                            v_isSharedCheck_4873_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4840_)) as u8;
                            if v_isSharedCheck_4873_ == 0 {
                                v___x_4868_ = v___x_4840_;
                                v_isShared_4869_ = v_isSharedCheck_4873_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4866_);
                                crate::leanh::lean_dec(v___x_4840_);
                                v___x_4868_ = crate::leanh::lean_box(0);
                                v_isShared_4869_ = v_isSharedCheck_4873_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4822_);
                        crate::leanh::lean_dec_ref(v___x_4818_);
                        v_a_4874_ = crate::leanh::lean_ctor_get(v___x_4834_, 0);
                        v_isSharedCheck_4881_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4834_)) as u8;
                        if v_isSharedCheck_4881_ == 0 {
                            v___x_4876_ = v___x_4834_;
                            v_isShared_4877_ = v_isSharedCheck_4881_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4874_);
                            crate::leanh::lean_dec(v___x_4834_);
                            v___x_4876_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
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
                    v_reuseFailAlloc_4864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
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
                    v_reuseFailAlloc_4872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
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
                    v_reuseFailAlloc_4880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
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
    mut v___x_4882_: *mut crate::leanh::LeanObject,
    mut v_as_4883_: *mut crate::leanh::LeanObject,
    mut v_sz_4884_: *mut crate::leanh::LeanObject,
    mut v_i_4885_: *mut crate::leanh::LeanObject,
    mut v_b_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4894_: usize = 0;
    let mut v_i_boxed_4895_: usize = 0;
    let mut v_res_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4894_ = crate::leanh::lean_unbox_usize(v_sz_4884_);
    crate::leanh::lean_dec(v_sz_4884_);
    v_i_boxed_4895_ = crate::leanh::lean_unbox_usize(v_i_4885_);
    crate::leanh::lean_dec(v_i_4885_);
    v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_4882_, v_as_4883_, v_sz_boxed_4894_, v_i_boxed_4895_, v_b_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
    crate::leanh::lean_dec(v___y_4892_);
    crate::leanh::lean_dec_ref(v___y_4891_);
    crate::leanh::lean_dec(v___y_4890_);
    crate::leanh::lean_dec_ref(v___y_4889_);
    crate::leanh::lean_dec(v___y_4888_);
    crate::leanh::lean_dec_ref(v___y_4887_);
    crate::leanh::lean_dec_ref(v_as_4883_);
    return v_res_4896_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(
    mut v_msgData_4897_: *mut crate::leanh::LeanObject,
    mut v___y_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
    mut v___y_4901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4903_ = lean_st_ref_get(v___y_4901_);
    v_env_4904_ = crate::leanh::lean_ctor_get(v___x_4903_, 0);
    crate::leanh::lean_inc_ref(v_env_4904_);
    crate::leanh::lean_dec(v___x_4903_);
    v___x_4905_ = lean_st_ref_get(v___y_4899_);
    v_mctx_4906_ = crate::leanh::lean_ctor_get(v___x_4905_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4906_);
    crate::leanh::lean_dec(v___x_4905_);
    v_lctx_4907_ = crate::leanh::lean_ctor_get(v___y_4898_, 2);
    v_options_4908_ = crate::leanh::lean_ctor_get(v___y_4900_, 2);
    crate::leanh::lean_inc_ref(v_options_4908_);
    crate::leanh::lean_inc_ref(v_lctx_4907_);
    v___x_4909_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4909_, 0, v_env_4904_);
    crate::leanh::lean_ctor_set(v___x_4909_, 1, v_mctx_4906_);
    crate::leanh::lean_ctor_set(v___x_4909_, 2, v_lctx_4907_);
    crate::leanh::lean_ctor_set(v___x_4909_, 3, v_options_4908_);
    v___x_4910_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4910_, 0, v___x_4909_);
    crate::leanh::lean_ctor_set(v___x_4910_, 1, v_msgData_4897_);
    v___x_4911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4911_, 0, v___x_4910_);
    return v___x_4911_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(
    mut v_msgData_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
    crate::leanh::lean_dec(v___y_4916_);
    crate::leanh::lean_dec_ref(v___y_4915_);
    crate::leanh::lean_dec(v___y_4914_);
    crate::leanh::lean_dec_ref(v___y_4913_);
    return v_res_4918_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ = crate::leanh::lean_box(1);
    v___x_4920_ = l_Lean_MessageData_ofFormat(v___x_4919_);
    return v___x_4920_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4924_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2;
    v___x_4925_ = l_Lean_MessageData_ofFormat(v___x_4924_);
    return v___x_4925_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(
    mut v_x_4926_: *mut crate::leanh::LeanObject,
    mut v_x_4927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4932_: u8 = 0;
    let mut v_before_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_unused_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4927_) == 0 {
                    return v_x_4926_;
                } else {
                    v_head_4928_ = crate::leanh::lean_ctor_get(v_x_4927_, 0);
                    v_tail_4929_ = crate::leanh::lean_ctor_get(v_x_4927_, 1);
                    v_isSharedCheck_4951_ = (!crate::leanh::lean_is_exclusive(v_x_4927_)) as u8;
                    if v_isSharedCheck_4951_ == 0 {
                        v___x_4931_ = v_x_4927_;
                        v_isShared_4932_ = v_isSharedCheck_4951_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4929_);
                        crate::leanh::lean_inc(v_head_4928_);
                        crate::leanh::lean_dec(v_x_4927_);
                        v___x_4931_ = crate::leanh::lean_box(0);
                        v_isShared_4932_ = v_isSharedCheck_4951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4933_ = crate::leanh::lean_ctor_get(v_head_4928_, 0);
                v_isSharedCheck_4949_ = (!crate::leanh::lean_is_exclusive(v_head_4928_)) as u8;
                if v_isSharedCheck_4949_ == 0 {
                    v_unused_4950_ = crate::leanh::lean_ctor_get(v_head_4928_, 1);
                    crate::leanh::lean_dec(v_unused_4950_);
                    v___x_4935_ = v_head_4928_;
                    v_isShared_4936_ = v_isSharedCheck_4949_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_4933_);
                    crate::leanh::lean_dec(v_head_4928_);
                    v___x_4935_ = crate::leanh::lean_box(0);
                    v_isShared_4936_ = v_isSharedCheck_4949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4937_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
                if v_isShared_4936_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4935_, 7);
                    crate::leanh::lean_ctor_set(v___x_4935_, 1, v___x_4937_);
                    crate::leanh::lean_ctor_set(v___x_4935_, 0, v_x_4926_);
                    v___x_4939_ = v___x_4935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_x_4926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 1, v___x_4937_);
                    v___x_4939_ = v_reuseFailAlloc_4948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4940_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
                if v_isShared_4932_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4931_, 7);
                    crate::leanh::lean_ctor_set(v___x_4931_, 1, v___x_4940_);
                    crate::leanh::lean_ctor_set(v___x_4931_, 0, v___x_4939_);
                    v___x_4942_ = v___x_4931_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 1, v___x_4940_);
                    v___x_4942_ = v_reuseFailAlloc_4947_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4943_ = l_Lean_MessageData_ofSyntax(v_before_4933_);
                v___x_4944_ = l_Lean_indentD(v___x_4943_);
                v___x_4945_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4942_);
                crate::leanh::lean_ctor_set(v___x_4945_, 1, v___x_4944_);
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
    mut v_opts_4952_: *mut crate::leanh::LeanObject,
    mut v_opt_4953_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4954_ = crate::leanh::lean_ctor_get(v_opt_4953_, 0);
    v_defValue_4955_ = crate::leanh::lean_ctor_get(v_opt_4953_, 1);
    v_map_4956_ = crate::leanh::lean_ctor_get(v_opts_4952_, 0);
    v___x_4957_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4956_,
            v_name_4954_,
        );
    if crate::leanh::lean_obj_tag(v___x_4957_) == 0 {
        let mut v___x_4958_: u8 = 0;
        v___x_4958_ = (crate::leanh::lean_unbox(v_defValue_4955_) as u8);
        return v___x_4958_;
    } else {
        let mut v_val_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4959_ = crate::leanh::lean_ctor_get(v___x_4957_, 0);
        crate::leanh::lean_inc(v_val_4959_);
        crate::leanh::lean_dec_ref_known(v___x_4957_, 1);
        if crate::leanh::lean_obj_tag(v_val_4959_) == 1 {
            let mut v_v_4960_: u8 = 0;
            v_v_4960_ = crate::leanh::lean_ctor_get_uint8(v_val_4959_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4959_, 0);
            return v_v_4960_;
        } else {
            let mut v___x_4961_: u8 = 0;
            crate::leanh::lean_dec(v_val_4959_);
            v___x_4961_ = (crate::leanh::lean_unbox(v_defValue_4955_) as u8);
            return v___x_4961_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(
    mut v_opts_4962_: *mut crate::leanh::LeanObject,
    mut v_opt_4963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4964_: u8 = 0;
    let mut v_r_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4964_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_4962_, v_opt_4963_);
    crate::leanh::lean_dec_ref(v_opt_4963_);
    crate::leanh::lean_dec_ref(v_opts_4962_);
    v_r_4965_ = crate::leanh::lean_box((v_res_4964_) as usize);
    return v_r_4965_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4969_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1;
    v___x_4970_ = l_Lean_MessageData_ofFormat(v___x_4969_);
    return v___x_4970_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(
    mut v_msgData_4971_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: u8 = 0;
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_unused_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4975_ = crate::leanh::lean_ctor_get(v___y_4973_, 2);
                v___x_4976_ = l_Lean_Elab_pp_macroStack;
                v___x_4977_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_4975_, v___x_4976_);
                if v___x_4977_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_4972_);
                    v___x_4978_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4978_, 0, v_msgData_4971_);
                    return v___x_4978_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_4972_) == 0 {
                        v___x_4979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4979_, 0, v_msgData_4971_);
                        return v___x_4979_;
                    } else {
                        v_head_4980_ = crate::leanh::lean_ctor_get(v_macroStack_4972_, 0);
                        crate::leanh::lean_inc(v_head_4980_);
                        v_after_4981_ = crate::leanh::lean_ctor_get(v_head_4980_, 1);
                        v_isSharedCheck_4996_ =
                            (!crate::leanh::lean_is_exclusive(v_head_4980_)) as u8;
                        if v_isSharedCheck_4996_ == 0 {
                            v_unused_4997_ = crate::leanh::lean_ctor_get(v_head_4980_, 0);
                            crate::leanh::lean_dec(v_unused_4997_);
                            v___x_4983_ = v_head_4980_;
                            v_isShared_4984_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_4981_);
                            crate::leanh::lean_dec(v_head_4980_);
                            v___x_4983_ = crate::leanh::lean_box(0);
                            v_isShared_4984_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
                if v_isShared_4984_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4983_, 7);
                    crate::leanh::lean_ctor_set(v___x_4983_, 1, v___x_4985_);
                    crate::leanh::lean_ctor_set(v___x_4983_, 0, v_msgData_4971_);
                    v___x_4987_ = v___x_4983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4995_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_msgData_4971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 1, v___x_4985_);
                    v___x_4987_ = v_reuseFailAlloc_4995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4988_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
                v___x_4989_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4989_, 0, v___x_4987_);
                crate::leanh::lean_ctor_set(v___x_4989_, 1, v___x_4988_);
                v___x_4990_ = l_Lean_MessageData_ofSyntax(v_after_4981_);
                v___x_4991_ = l_Lean_indentD(v___x_4990_);
                v_msgData_4992_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_4992_, 0, v___x_4989_);
                crate::leanh::lean_ctor_set(v_msgData_4992_, 1, v___x_4991_);
                v___x_4993_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_4992_, v_macroStack_4972_);
                v___x_4994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4994_, 0, v___x_4993_);
                return v___x_4994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(
    mut v_msgData_4998_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_4998_, v_macroStack_4999_, v___y_5000_);
    crate::leanh::lean_dec_ref(v___y_5000_);
    return v_res_5002_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
    mut v_msg_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5011_ = crate::leanh::lean_ctor_get(v___y_5008_, 5);
                v___x_5012_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_5003_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
                v_a_5013_ = crate::leanh::lean_ctor_get(v___x_5012_, 0);
                crate::leanh::lean_inc(v_a_5013_);
                crate::leanh::lean_dec_ref(v___x_5012_);
                v_macroStack_5014_ = crate::leanh::lean_ctor_get(v___y_5004_, 1);
                v___x_5015_ = l_Lean_Elab_getBetterRef(v_ref_5011_, v_macroStack_5014_);
                crate::leanh::lean_inc(v_macroStack_5014_);
                v___x_5016_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_5013_, v_macroStack_5014_, v___y_5008_);
                v_a_5017_ = crate::leanh::lean_ctor_get(v___x_5016_, 0);
                v_isSharedCheck_5025_ = (!crate::leanh::lean_is_exclusive(v___x_5016_)) as u8;
                if v_isSharedCheck_5025_ == 0 {
                    v___x_5019_ = v___x_5016_;
                    v_isShared_5020_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5017_);
                    crate::leanh::lean_dec(v___x_5016_);
                    v___x_5019_ = crate::leanh::lean_box(0);
                    v_isShared_5020_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5021_, 0, v___x_5015_);
                crate::leanh::lean_ctor_set(v___x_5021_, 1, v_a_5017_);
                if v_isShared_5020_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5019_, 1);
                    crate::leanh::lean_ctor_set(v___x_5019_, 0, v___x_5021_);
                    v___x_5023_ = v___x_5019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
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
    mut v_msg_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5034_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
        v_msg_5026_,
        v___y_5027_,
        v___y_5028_,
        v___y_5029_,
        v___y_5030_,
        v___y_5031_,
        v___y_5032_,
    );
    crate::leanh::lean_dec(v___y_5032_);
    crate::leanh::lean_dec_ref(v___y_5031_);
    crate::leanh::lean_dec(v___y_5030_);
    crate::leanh::lean_dec_ref(v___y_5029_);
    crate::leanh::lean_dec(v___y_5028_);
    crate::leanh::lean_dec_ref(v___y_5027_);
    return v_res_5034_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5040_ = crate::leanh::lean_box(0);
    v___x_5041_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__2;
    v___x_5042_ = l_Lean_mkConst(v___x_5041_, v___x_5040_);
    return v___x_5042_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5044_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__4;
    v___x_5045_ = l_Lean_stringToMessageData(v___x_5044_);
    return v___x_5045_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5047_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__6;
    v___x_5048_ = l_Lean_stringToMessageData(v___x_5047_);
    return v___x_5048_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__9;
    v___x_5053_ = l_Lean_MessageData_ofFormat(v___x_5052_);
    return v___x_5053_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__3(
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v_monadInfo_5055_: *mut crate::leanh::LeanObject,
    mut v_returnsEarly_5056_: u8,
    mut v___x_5057_: *mut crate::leanh::LeanObject,
    mut v_a_5058_: *mut crate::leanh::LeanObject,
    mut v___x_5059_: u8,
    mut v_e_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defs_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5076_: usize = 0;
    let mut v___x_5077_: usize = 0;
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5084_: u8 = 0;
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_unused_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_returnVar_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut v_val_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut v___y_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5092_ = lean_mk_empty_array_with_capacity(v___x_5057_);
                if crate::leanh::lean_obj_tag(v_e_5060_) == 0 {
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
                if crate::leanh::lean_obj_tag(v___x_5078_) == 0 {
                    if v_returnsEarly_5056_ == 0 {
                        return v___x_5078_;
                    } else {
                        v_a_5079_ = crate::leanh::lean_ctor_get(v___x_5078_, 0);
                        crate::leanh::lean_inc(v_a_5079_);
                        v___x_5080_ = lean_array_get_size(v___y_5054_);
                        v___x_5081_ = lean_nat_dec_eq(v___x_5080_, v___x_5057_);
                        if v___x_5081_ == 0 {
                            crate::leanh::lean_dec(v_a_5079_);
                            return v___x_5078_;
                        } else {
                            v_isSharedCheck_5090_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5078_)) as u8;
                            if v_isSharedCheck_5090_ == 0 {
                                v_unused_5091_ = crate::leanh::lean_ctor_get(v___x_5078_, 0);
                                crate::leanh::lean_dec(v_unused_5091_);
                                v___x_5083_ = v___x_5078_;
                                v_isShared_5084_ = v_isSharedCheck_5090_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5078_);
                                v___x_5083_ = crate::leanh::lean_box(0);
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
                v___x_5085_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once),
                    _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3,
                );
                v___x_5086_ = lean_array_push(v_a_5079_, v___x_5085_);
                if v_isShared_5084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5083_, 0, v___x_5086_);
                    v___x_5088_ = v___x_5083_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
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
                    crate::leanh::lean_dec(v_e_5060_);
                    crate::leanh::lean_dec_ref(v_a_5058_);
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
                    if crate::leanh::lean_obj_tag(v_e_5060_) == 0 {
                        v_resultType_5103_ = crate::leanh::lean_ctor_get(v_a_5058_, 0);
                        crate::leanh::lean_inc_ref(v_resultType_5103_);
                        crate::leanh::lean_dec_ref(v_a_5058_);
                        v___x_5104_ = l_Lean_Meta_mkNone(
                            v_resultType_5103_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5104_) == 0 {
                            v_a_5105_ = crate::leanh::lean_ctor_get(v___x_5104_, 0);
                            crate::leanh::lean_inc(v_a_5105_);
                            crate::leanh::lean_dec_ref_known(v___x_5104_, 1);
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
                            crate::leanh::lean_dec_ref(v___x_5092_);
                            crate::leanh::lean_dec_ref(v_monadInfo_5055_);
                            v_a_5106_ = crate::leanh::lean_ctor_get(v___x_5104_, 0);
                            v_isSharedCheck_5113_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5104_)) as u8;
                            if v_isSharedCheck_5113_ == 0 {
                                v___x_5108_ = v___x_5104_;
                                v_isShared_5109_ = v_isSharedCheck_5113_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5106_);
                                crate::leanh::lean_dec(v___x_5104_);
                                v___x_5108_ = crate::leanh::lean_box(0);
                                v_isShared_5109_ = v_isSharedCheck_5113_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_val_5114_ = crate::leanh::lean_ctor_get(v_e_5060_, 0);
                        crate::leanh::lean_inc(v_val_5114_);
                        crate::leanh::lean_dec_ref_known(v_e_5060_, 1);
                        v_resultType_5115_ = crate::leanh::lean_ctor_get(v_a_5058_, 0);
                        crate::leanh::lean_inc_ref(v_resultType_5115_);
                        crate::leanh::lean_dec_ref(v_a_5058_);
                        v___x_5116_ = l_Lean_Meta_mkSome(
                            v_resultType_5115_,
                            v_val_5114_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5116_) == 0 {
                            v_a_5117_ = crate::leanh::lean_ctor_get(v___x_5116_, 0);
                            crate::leanh::lean_inc(v_a_5117_);
                            crate::leanh::lean_dec_ref_known(v___x_5116_, 1);
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
                            crate::leanh::lean_dec_ref(v___x_5092_);
                            crate::leanh::lean_dec_ref(v_monadInfo_5055_);
                            v_a_5118_ = crate::leanh::lean_ctor_get(v___x_5116_, 0);
                            v_isSharedCheck_5125_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5116_)) as u8;
                            if v_isSharedCheck_5125_ == 0 {
                                v___x_5120_ = v___x_5116_;
                                v_isShared_5121_ = v_isSharedCheck_5125_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5118_);
                                crate::leanh::lean_dec(v___x_5116_);
                                v___x_5120_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
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
                    v_reuseFailAlloc_5124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
                    v___x_5123_ = v_reuseFailAlloc_5124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5123_;
            }
            10 => {
                crate::leanh::lean_inc_ref(v___y_5127_);
                v___x_5129_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5129_, 0, v___y_5127_);
                crate::leanh::lean_ctor_set(v___x_5129_, 1, v___y_5128_);
                v___x_5130_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once),
                    _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5,
                );
                v___x_5131_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                crate::leanh::lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                v___x_5132_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
                    v___x_5131_,
                    v___y_5061_,
                    v___y_5062_,
                    v___y_5063_,
                    v___y_5064_,
                    v___y_5065_,
                    v___y_5066_,
                );
                v_a_5133_ = crate::leanh::lean_ctor_get(v___x_5132_, 0);
                v_isSharedCheck_5140_ = (!crate::leanh::lean_is_exclusive(v___x_5132_)) as u8;
                if v_isSharedCheck_5140_ == 0 {
                    v___x_5135_ = v___x_5132_;
                    v_isShared_5136_ = v_isSharedCheck_5140_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5133_);
                    crate::leanh::lean_dec(v___x_5132_);
                    v___x_5135_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
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
                    crate::leanh::lean_dec_ref(v___x_5092_);
                    crate::leanh::lean_dec_ref(v_a_5058_);
                    crate::leanh::lean_dec_ref(v_monadInfo_5055_);
                    v___x_5142_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once),
                        _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7,
                    );
                    if crate::leanh::lean_obj_tag(v_e_5060_) == 0 {
                        v___x_5143_ = crate::leanh::lean_obj_once(
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
                        v_val_5144_ = crate::leanh::lean_ctor_get(v_e_5060_, 0);
                        crate::leanh::lean_inc(v_val_5144_);
                        crate::leanh::lean_dec_ref_known(v_e_5060_, 1);
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
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v_monadInfo_5147_: *mut crate::leanh::LeanObject,
    mut v_returnsEarly_5148_: *mut crate::leanh::LeanObject,
    mut v___x_5149_: *mut crate::leanh::LeanObject,
    mut v_a_5150_: *mut crate::leanh::LeanObject,
    mut v___x_5151_: *mut crate::leanh::LeanObject,
    mut v_e_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_returnsEarly_boxed_5160_: u8 = 0;
    let mut v___x_71505__boxed_5161_: u8 = 0;
    let mut v_res_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_returnsEarly_boxed_5160_ = (crate::leanh::lean_unbox(v_returnsEarly_5148_) as u8);
    v___x_71505__boxed_5161_ = (crate::leanh::lean_unbox(v___x_5151_) as u8);
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
    crate::leanh::lean_dec(v___y_5158_);
    crate::leanh::lean_dec_ref(v___y_5157_);
    crate::leanh::lean_dec(v___y_5156_);
    crate::leanh::lean_dec_ref(v___y_5155_);
    crate::leanh::lean_dec(v___y_5154_);
    crate::leanh::lean_dec_ref(v___y_5153_);
    crate::leanh::lean_dec(v___x_5149_);
    crate::leanh::lean_dec_ref(v___y_5146_);
    return v_res_5162_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__4(
    mut v___f_5164_: *mut crate::leanh::LeanObject,
    mut v_u_5165_: *mut crate::leanh::LeanObject,
    mut v___x_5166_: *mut crate::leanh::LeanObject,
    mut v___x_5167_: *mut crate::leanh::LeanObject,
    mut v_snd_5168_: *mut crate::leanh::LeanObject,
    mut v___x_5169_: *mut crate::leanh::LeanObject,
    mut v_e_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5193_: u8 = 0;
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_a_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5179_, 0, v_e_5170_);
                crate::leanh::lean_inc(v___y_5177_);
                crate::leanh::lean_inc_ref(v___y_5176_);
                crate::leanh::lean_inc(v___y_5175_);
                crate::leanh::lean_inc_ref(v___y_5174_);
                crate::leanh::lean_inc(v___y_5173_);
                crate::leanh::lean_inc_ref(v___y_5172_);
                v___x_5180_ = crate::leanh::lean_apply_8(
                    v___f_5164_,
                    v___x_5179_,
                    v___y_5172_,
                    v___y_5173_,
                    v___y_5174_,
                    v___y_5175_,
                    v___y_5176_,
                    v___y_5177_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5180_) == 0 {
                    v_a_5181_ = crate::leanh::lean_ctor_get(v___x_5180_, 0);
                    crate::leanh::lean_inc(v_a_5181_);
                    crate::leanh::lean_dec_ref_known(v___x_5180_, 1);
                    v___x_5182_ = l_Lean_Meta_mkProdMkN(
                        v_a_5181_,
                        v_u_5165_,
                        v___y_5174_,
                        v___y_5175_,
                        v___y_5176_,
                        v___y_5177_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5182_) == 0 {
                        v_a_5183_ = crate::leanh::lean_ctor_get(v___x_5182_, 0);
                        crate::leanh::lean_inc(v_a_5183_);
                        crate::leanh::lean_dec_ref_known(v___x_5182_, 1);
                        v_fst_5184_ = crate::leanh::lean_ctor_get(v_a_5183_, 0);
                        crate::leanh::lean_inc(v_fst_5184_);
                        crate::leanh::lean_dec(v_a_5183_);
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
                        crate::leanh::lean_dec_ref(v___x_5169_);
                        crate::leanh::lean_dec_ref(v_snd_5168_);
                        crate::leanh::lean_dec(v___x_5167_);
                        crate::leanh::lean_dec_ref(v___x_5166_);
                        v_a_5190_ = crate::leanh::lean_ctor_get(v___x_5182_, 0);
                        v_isSharedCheck_5197_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5182_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5192_ = v___x_5182_;
                            v_isShared_5193_ = v_isSharedCheck_5197_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5190_);
                            crate::leanh::lean_dec(v___x_5182_);
                            v___x_5192_ = crate::leanh::lean_box(0);
                            v_isShared_5193_ = v_isSharedCheck_5197_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5169_);
                    crate::leanh::lean_dec_ref(v_snd_5168_);
                    crate::leanh::lean_dec(v___x_5167_);
                    crate::leanh::lean_dec_ref(v___x_5166_);
                    crate::leanh::lean_dec(v_u_5165_);
                    v_a_5198_ = crate::leanh::lean_ctor_get(v___x_5180_, 0);
                    v_isSharedCheck_5205_ = (!crate::leanh::lean_is_exclusive(v___x_5180_)) as u8;
                    if v_isSharedCheck_5205_ == 0 {
                        v___x_5200_ = v___x_5180_;
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5198_);
                        crate::leanh::lean_dec(v___x_5180_);
                        v___x_5200_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
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
                    v_reuseFailAlloc_5204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
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
    mut v___f_5206_: *mut crate::leanh::LeanObject,
    mut v_u_5207_: *mut crate::leanh::LeanObject,
    mut v___x_5208_: *mut crate::leanh::LeanObject,
    mut v___x_5209_: *mut crate::leanh::LeanObject,
    mut v_snd_5210_: *mut crate::leanh::LeanObject,
    mut v___x_5211_: *mut crate::leanh::LeanObject,
    mut v_e_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
    mut v___y_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
    mut v___y_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5219_);
    crate::leanh::lean_dec_ref(v___y_5218_);
    crate::leanh::lean_dec(v___y_5217_);
    crate::leanh::lean_dec_ref(v___y_5216_);
    crate::leanh::lean_dec(v___y_5215_);
    crate::leanh::lean_dec_ref(v___y_5214_);
    crate::leanh::lean_dec_ref(v___y_5213_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__5(
    mut v___f_5223_: *mut crate::leanh::LeanObject,
    mut v___x_5224_: *mut crate::leanh::LeanObject,
    mut v_u_5225_: *mut crate::leanh::LeanObject,
    mut v___x_5226_: *mut crate::leanh::LeanObject,
    mut v___x_5227_: *mut crate::leanh::LeanObject,
    mut v_snd_5228_: *mut crate::leanh::LeanObject,
    mut v___x_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5236_);
                crate::leanh::lean_inc_ref(v___y_5235_);
                crate::leanh::lean_inc(v___y_5234_);
                crate::leanh::lean_inc_ref(v___y_5233_);
                crate::leanh::lean_inc(v___y_5232_);
                crate::leanh::lean_inc_ref(v___y_5231_);
                v___x_5238_ = crate::leanh::lean_apply_8(
                    v___f_5223_,
                    v___x_5224_,
                    v___y_5231_,
                    v___y_5232_,
                    v___y_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5238_) == 0 {
                    v_a_5239_ = crate::leanh::lean_ctor_get(v___x_5238_, 0);
                    crate::leanh::lean_inc(v_a_5239_);
                    crate::leanh::lean_dec_ref_known(v___x_5238_, 1);
                    v___x_5240_ = l_Lean_Meta_mkProdMkN(
                        v_a_5239_,
                        v_u_5225_,
                        v___y_5233_,
                        v___y_5234_,
                        v___y_5235_,
                        v___y_5236_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5240_) == 0 {
                        v_a_5241_ = crate::leanh::lean_ctor_get(v___x_5240_, 0);
                        crate::leanh::lean_inc(v_a_5241_);
                        crate::leanh::lean_dec_ref_known(v___x_5240_, 1);
                        v_fst_5242_ = crate::leanh::lean_ctor_get(v_a_5241_, 0);
                        crate::leanh::lean_inc(v_fst_5242_);
                        crate::leanh::lean_dec(v_a_5241_);
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
                        crate::leanh::lean_dec_ref(v___x_5229_);
                        crate::leanh::lean_dec_ref(v_snd_5228_);
                        crate::leanh::lean_dec(v___x_5227_);
                        crate::leanh::lean_dec_ref(v___x_5226_);
                        v_a_5248_ = crate::leanh::lean_ctor_get(v___x_5240_, 0);
                        v_isSharedCheck_5255_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5240_)) as u8;
                        if v_isSharedCheck_5255_ == 0 {
                            v___x_5250_ = v___x_5240_;
                            v_isShared_5251_ = v_isSharedCheck_5255_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5248_);
                            crate::leanh::lean_dec(v___x_5240_);
                            v___x_5250_ = crate::leanh::lean_box(0);
                            v_isShared_5251_ = v_isSharedCheck_5255_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5229_);
                    crate::leanh::lean_dec_ref(v_snd_5228_);
                    crate::leanh::lean_dec(v___x_5227_);
                    crate::leanh::lean_dec_ref(v___x_5226_);
                    crate::leanh::lean_dec(v_u_5225_);
                    v_a_5256_ = crate::leanh::lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5263_ = (!crate::leanh::lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5263_ == 0 {
                        v___x_5258_ = v___x_5238_;
                        v_isShared_5259_ = v_isSharedCheck_5263_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5256_);
                        crate::leanh::lean_dec(v___x_5238_);
                        v___x_5258_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
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
                    v_reuseFailAlloc_5262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
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
    mut v___f_5264_: *mut crate::leanh::LeanObject,
    mut v___x_5265_: *mut crate::leanh::LeanObject,
    mut v_u_5266_: *mut crate::leanh::LeanObject,
    mut v___x_5267_: *mut crate::leanh::LeanObject,
    mut v___x_5268_: *mut crate::leanh::LeanObject,
    mut v_snd_5269_: *mut crate::leanh::LeanObject,
    mut v___x_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
    mut v___y_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5277_);
    crate::leanh::lean_dec_ref(v___y_5276_);
    crate::leanh::lean_dec(v___y_5275_);
    crate::leanh::lean_dec_ref(v___y_5274_);
    crate::leanh::lean_dec(v___y_5273_);
    crate::leanh::lean_dec_ref(v___y_5272_);
    crate::leanh::lean_dec_ref(v___y_5271_);
    return v_res_5279_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__6(
    mut v___f_5280_: *mut crate::leanh::LeanObject,
    mut v___x_5281_: *mut crate::leanh::LeanObject,
    mut v_u_5282_: *mut crate::leanh::LeanObject,
    mut v___x_5283_: *mut crate::leanh::LeanObject,
    mut v___x_5284_: *mut crate::leanh::LeanObject,
    mut v_snd_5285_: *mut crate::leanh::LeanObject,
    mut v___x_5286_: *mut crate::leanh::LeanObject,
    mut v___y_5287_: *mut crate::leanh::LeanObject,
    mut v___y_5288_: *mut crate::leanh::LeanObject,
    mut v___y_5289_: *mut crate::leanh::LeanObject,
    mut v___y_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5308_: u8 = 0;
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut v_a_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5316_: u8 = 0;
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5293_);
                crate::leanh::lean_inc_ref(v___y_5292_);
                crate::leanh::lean_inc(v___y_5291_);
                crate::leanh::lean_inc_ref(v___y_5290_);
                crate::leanh::lean_inc(v___y_5289_);
                crate::leanh::lean_inc_ref(v___y_5288_);
                v___x_5295_ = crate::leanh::lean_apply_8(
                    v___f_5280_,
                    v___x_5281_,
                    v___y_5288_,
                    v___y_5289_,
                    v___y_5290_,
                    v___y_5291_,
                    v___y_5292_,
                    v___y_5293_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5295_) == 0 {
                    v_a_5296_ = crate::leanh::lean_ctor_get(v___x_5295_, 0);
                    crate::leanh::lean_inc(v_a_5296_);
                    crate::leanh::lean_dec_ref_known(v___x_5295_, 1);
                    v___x_5297_ = l_Lean_Meta_mkProdMkN(
                        v_a_5296_,
                        v_u_5282_,
                        v___y_5290_,
                        v___y_5291_,
                        v___y_5292_,
                        v___y_5293_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5297_) == 0 {
                        v_a_5298_ = crate::leanh::lean_ctor_get(v___x_5297_, 0);
                        crate::leanh::lean_inc(v_a_5298_);
                        crate::leanh::lean_dec_ref_known(v___x_5297_, 1);
                        v_fst_5299_ = crate::leanh::lean_ctor_get(v_a_5298_, 0);
                        crate::leanh::lean_inc(v_fst_5299_);
                        crate::leanh::lean_dec(v_a_5298_);
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
                        crate::leanh::lean_dec_ref(v___x_5286_);
                        crate::leanh::lean_dec_ref(v_snd_5285_);
                        crate::leanh::lean_dec(v___x_5284_);
                        crate::leanh::lean_dec_ref(v___x_5283_);
                        v_a_5305_ = crate::leanh::lean_ctor_get(v___x_5297_, 0);
                        v_isSharedCheck_5312_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5297_)) as u8;
                        if v_isSharedCheck_5312_ == 0 {
                            v___x_5307_ = v___x_5297_;
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5305_);
                            crate::leanh::lean_dec(v___x_5297_);
                            v___x_5307_ = crate::leanh::lean_box(0);
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5286_);
                    crate::leanh::lean_dec_ref(v_snd_5285_);
                    crate::leanh::lean_dec(v___x_5284_);
                    crate::leanh::lean_dec_ref(v___x_5283_);
                    crate::leanh::lean_dec(v_u_5282_);
                    v_a_5313_ = crate::leanh::lean_ctor_get(v___x_5295_, 0);
                    v_isSharedCheck_5320_ = (!crate::leanh::lean_is_exclusive(v___x_5295_)) as u8;
                    if v_isSharedCheck_5320_ == 0 {
                        v___x_5315_ = v___x_5295_;
                        v_isShared_5316_ = v_isSharedCheck_5320_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5313_);
                        crate::leanh::lean_dec(v___x_5295_);
                        v___x_5315_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
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
                    v_reuseFailAlloc_5319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
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
    mut v___f_5321_: *mut crate::leanh::LeanObject,
    mut v___x_5322_: *mut crate::leanh::LeanObject,
    mut v_u_5323_: *mut crate::leanh::LeanObject,
    mut v___x_5324_: *mut crate::leanh::LeanObject,
    mut v___x_5325_: *mut crate::leanh::LeanObject,
    mut v_snd_5326_: *mut crate::leanh::LeanObject,
    mut v___x_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
    mut v___y_5333_: *mut crate::leanh::LeanObject,
    mut v___y_5334_: *mut crate::leanh::LeanObject,
    mut v___y_5335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5334_);
    crate::leanh::lean_dec_ref(v___y_5333_);
    crate::leanh::lean_dec(v___y_5332_);
    crate::leanh::lean_dec_ref(v___y_5331_);
    crate::leanh::lean_dec(v___y_5330_);
    crate::leanh::lean_dec_ref(v___y_5329_);
    crate::leanh::lean_dec_ref(v___y_5328_);
    return v_res_5336_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__7(
    mut v___x_5337_: *mut crate::leanh::LeanObject,
    mut v___f_5338_: *mut crate::leanh::LeanObject,
    mut v___f_5339_: *mut crate::leanh::LeanObject,
    mut v___x_5340_: *mut crate::leanh::LeanObject,
    mut v___x_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_monadInfo_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVars_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVarDefs_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contInfo_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deadCode_5354_: u8 = 0;
    let mut v_ops_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5363_: u8 = 0;
    let mut v_unused_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_monadInfo_5350_ = crate::leanh::lean_ctor_get(v___y_5342_, 0);
                v_mutVars_5351_ = crate::leanh::lean_ctor_get(v___y_5342_, 1);
                v_mutVarDefs_5352_ = crate::leanh::lean_ctor_get(v___y_5342_, 2);
                v_contInfo_5353_ = crate::leanh::lean_ctor_get(v___y_5342_, 4);
                v_deadCode_5354_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5342_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_ops_5355_ = crate::leanh::lean_ctor_get(v___y_5342_, 5);
                v_isSharedCheck_5363_ = (!crate::leanh::lean_is_exclusive(v___y_5342_)) as u8;
                if v_isSharedCheck_5363_ == 0 {
                    v_unused_5364_ = crate::leanh::lean_ctor_get(v___y_5342_, 3);
                    crate::leanh::lean_dec(v_unused_5364_);
                    v___x_5357_ = v___y_5342_;
                    v_isShared_5358_ = v_isSharedCheck_5363_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ops_5355_);
                    crate::leanh::lean_inc(v_contInfo_5353_);
                    crate::leanh::lean_inc(v_mutVarDefs_5352_);
                    crate::leanh::lean_inc(v_mutVars_5351_);
                    crate::leanh::lean_inc(v_monadInfo_5350_);
                    crate::leanh::lean_dec(v___y_5342_);
                    v___x_5357_ = crate::leanh::lean_box(0);
                    v_isShared_5358_ = v_isSharedCheck_5363_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5357_, 3, v___x_5337_);
                    v___x_5360_ = v___x_5357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5362_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_monadInfo_5350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 1, v_mutVars_5351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 2, v_mutVarDefs_5352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 3, v___x_5337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 4, v_contInfo_5353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 5, v_ops_5355_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5362_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
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
                crate::leanh::lean_dec_ref(v___x_5360_);
                return v___x_5361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__7___boxed(
    mut v___x_5365_: *mut crate::leanh::LeanObject,
    mut v___f_5366_: *mut crate::leanh::LeanObject,
    mut v___f_5367_: *mut crate::leanh::LeanObject,
    mut v___x_5368_: *mut crate::leanh::LeanObject,
    mut v___x_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5376_);
    crate::leanh::lean_dec_ref(v___y_5375_);
    crate::leanh::lean_dec(v___y_5374_);
    crate::leanh::lean_dec_ref(v___y_5373_);
    crate::leanh::lean_dec(v___y_5372_);
    crate::leanh::lean_dec_ref(v___y_5371_);
    return v_res_5378_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__8(
    mut v_a_5382_: *mut crate::leanh::LeanObject,
    mut v_a_5383_: *mut crate::leanh::LeanObject,
    mut v_u_5384_: *mut crate::leanh::LeanObject,
    mut v_snd_5385_: *mut crate::leanh::LeanObject,
    mut v___f_5386_: *mut crate::leanh::LeanObject,
    mut v___x_5387_: *mut crate::leanh::LeanObject,
    mut v_body_5388_: *mut crate::leanh::LeanObject,
    mut v___x_5389_: u8,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v_xh_5391_: *mut crate::leanh::LeanObject,
    mut v_loopS_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
    mut v___y_5394_: *mut crate::leanh::LeanObject,
    mut v___y_5395_: *mut crate::leanh::LeanObject,
    mut v___y_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
    mut v___y_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_resultType_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_resultName_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: u8 = 0;
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_unused_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_unused_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_resultType_5401_ = crate::leanh::lean_ctor_get(v_a_5382_, 0);
                v_isSharedCheck_5438_ = (!crate::leanh::lean_is_exclusive(v_a_5382_)) as u8;
                if v_isSharedCheck_5438_ == 0 {
                    v_unused_5439_ = crate::leanh::lean_ctor_get(v_a_5382_, 1);
                    crate::leanh::lean_dec(v_unused_5439_);
                    v___x_5403_ = v_a_5382_;
                    v_isShared_5404_ = v_isSharedCheck_5438_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_resultType_5401_);
                    crate::leanh::lean_dec(v_a_5382_);
                    v___x_5403_ = crate::leanh::lean_box(0);
                    v_isShared_5404_ = v_isSharedCheck_5438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_resultName_5405_ = crate::leanh::lean_ctor_get(v_a_5383_, 0);
                v_resultType_5406_ = crate::leanh::lean_ctor_get(v_a_5383_, 1);
                v_isSharedCheck_5436_ = (!crate::leanh::lean_is_exclusive(v_a_5383_)) as u8;
                if v_isSharedCheck_5436_ == 0 {
                    v_unused_5437_ = crate::leanh::lean_ctor_get(v_a_5383_, 2);
                    crate::leanh::lean_dec(v_unused_5437_);
                    v___x_5408_ = v_a_5383_;
                    v_isShared_5409_ = v_isSharedCheck_5436_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_resultType_5406_);
                    crate::leanh::lean_inc(v_resultName_5405_);
                    crate::leanh::lean_dec(v_a_5383_);
                    v___x_5408_ = crate::leanh::lean_box(0);
                    v_isShared_5409_ = v_isSharedCheck_5436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5410_ = l_Lean_Expr_fvarId_x21(v_loopS_5392_);
                v___x_5411_ = l_Lean_Elab_Do_elabDoFor___lam__8___closed__0;
                v___x_5412_ = l_Lean_Elab_Do_elabDoFor___lam__8___closed__1;
                v___x_5413_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_u_5384_, 3);
                v___x_5414_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5414_, 0, v_u_5384_);
                crate::leanh::lean_ctor_set(v___x_5414_, 1, v___x_5413_);
                crate::leanh::lean_inc_ref_n(v___x_5414_, 3);
                v___x_5415_ = l_Lean_mkConst(v___x_5412_, v___x_5414_);
                crate::leanh::lean_inc_ref_n(v_snd_5385_, 3);
                v___x_5416_ = l_Lean_Expr_app___override(v___x_5415_, v_snd_5385_);
                crate::leanh::lean_inc_ref_n(v___x_5416_, 3);
                crate::leanh::lean_inc_ref_n(v___f_5386_, 2);
                v___f_5417_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__4___boxed as *mut core::ffi::c_void,
                    15,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_5417_, 0, v___f_5386_);
                crate::leanh::lean_closure_set(v___f_5417_, 1, v_u_5384_);
                crate::leanh::lean_closure_set(v___f_5417_, 2, v___x_5411_);
                crate::leanh::lean_closure_set(v___f_5417_, 3, v___x_5414_);
                crate::leanh::lean_closure_set(v___f_5417_, 4, v_snd_5385_);
                crate::leanh::lean_closure_set(v___f_5417_, 5, v___x_5416_);
                crate::leanh::lean_inc(v___x_5387_);
                v___f_5418_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__5___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_5418_, 0, v___f_5386_);
                crate::leanh::lean_closure_set(v___f_5418_, 1, v___x_5387_);
                crate::leanh::lean_closure_set(v___f_5418_, 2, v_u_5384_);
                crate::leanh::lean_closure_set(v___f_5418_, 3, v___x_5411_);
                crate::leanh::lean_closure_set(v___f_5418_, 4, v___x_5414_);
                crate::leanh::lean_closure_set(v___f_5418_, 5, v_snd_5385_);
                crate::leanh::lean_closure_set(v___f_5418_, 6, v___x_5416_);
                v___f_5419_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__6___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_5419_, 0, v___f_5386_);
                crate::leanh::lean_closure_set(v___f_5419_, 1, v___x_5387_);
                crate::leanh::lean_closure_set(v___f_5419_, 2, v_u_5384_);
                crate::leanh::lean_closure_set(v___f_5419_, 3, v___x_5411_);
                crate::leanh::lean_closure_set(v___f_5419_, 4, v___x_5414_);
                crate::leanh::lean_closure_set(v___f_5419_, 5, v_snd_5385_);
                crate::leanh::lean_closure_set(v___f_5419_, 6, v___x_5416_);
                if v_isShared_5404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5403_, 1, v___f_5417_);
                    v___x_5421_ = v___x_5403_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_resultType_5401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 1, v___f_5417_);
                    v___x_5421_ = v_reuseFailAlloc_5435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5422_ = 1;
                crate::leanh::lean_inc_ref(v___f_5418_);
                if v_isShared_5409_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5408_, 2, v___f_5418_);
                    v___x_5424_ = v___x_5408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5434_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_resultName_5405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_resultType_5406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 2, v___f_5418_);
                    v___x_5424_ = v_reuseFailAlloc_5434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5424_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5422_,
                );
                v___x_5425_ = crate::leanh::lean_box((v___x_5389_) as usize);
                v___x_5426_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_5426_, 0, v_body_5388_);
                crate::leanh::lean_closure_set(v___x_5426_, 1, v___x_5424_);
                crate::leanh::lean_closure_set(v___x_5426_, 2, v___x_5425_);
                v___f_5427_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__7___boxed as *mut core::ffi::c_void,
                    13,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_5427_, 0, v___x_5416_);
                crate::leanh::lean_closure_set(v___f_5427_, 1, v___f_5419_);
                crate::leanh::lean_closure_set(v___f_5427_, 2, v___f_5418_);
                crate::leanh::lean_closure_set(v___f_5427_, 3, v___x_5421_);
                crate::leanh::lean_closure_set(v___f_5427_, 4, v___x_5426_);
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
                if crate::leanh::lean_obj_tag(v___x_5428_) == 0 {
                    v_a_5429_ = crate::leanh::lean_ctor_get(v___x_5428_, 0);
                    crate::leanh::lean_inc(v_a_5429_);
                    crate::leanh::lean_dec_ref_known(v___x_5428_, 1);
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
                    crate::leanh::lean_dec_ref(v___x_5430_);
                    return v___x_5433_;
                } else {
                    crate::leanh::lean_dec_ref(v_loopS_5392_);
                    crate::leanh::lean_dec_ref(v_xh_5391_);
                    return v___x_5428_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__8___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5440_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_5441_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_u_5442_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_snd_5443_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_5444_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5445_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_body_5446_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5447_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5448_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_xh_5449_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_loopS_5450_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5451_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5452_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5453_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5454_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5455_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5456_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5457_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5458_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_72062__boxed_5459_: u8 = 0;
    let mut v_res_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_72062__boxed_5459_ = (crate::leanh::lean_unbox(v___x_5447_) as u8);
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
    crate::leanh::lean_dec(v___y_5457_);
    crate::leanh::lean_dec_ref(v___y_5456_);
    crate::leanh::lean_dec(v___y_5455_);
    crate::leanh::lean_dec_ref(v___y_5454_);
    crate::leanh::lean_dec(v___y_5453_);
    crate::leanh::lean_dec_ref(v___y_5452_);
    crate::leanh::lean_dec_ref(v___y_5451_);
    return v_res_5460_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__9(
    mut v___x_5461_: *mut crate::leanh::LeanObject,
    mut v___x_5462_: *mut crate::leanh::LeanObject,
    mut v_x_5463_: *mut crate::leanh::LeanObject,
    mut v_a_5464_: *mut crate::leanh::LeanObject,
    mut v_a_5465_: *mut crate::leanh::LeanObject,
    mut v_u_5466_: *mut crate::leanh::LeanObject,
    mut v_snd_5467_: *mut crate::leanh::LeanObject,
    mut v___f_5468_: *mut crate::leanh::LeanObject,
    mut v___x_5469_: *mut crate::leanh::LeanObject,
    mut v_body_5470_: *mut crate::leanh::LeanObject,
    mut v___x_5471_: u8,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v_a_5473_: *mut crate::leanh::LeanObject,
    mut v_h_x3f_5474_: *mut crate::leanh::LeanObject,
    mut v___x_5475_: *mut crate::leanh::LeanObject,
    mut v_xh_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: u8 = 0;
    let mut v___x_5498_: u8 = 0;
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5506_: u8 = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5510_: u8 = 0;
    let mut v_a_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5485_ = lean_array_get_borrowed(v___x_5461_, v_xh_5476_, v___x_5462_);
                crate::leanh::lean_inc(v___x_5485_);
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
                if crate::leanh::lean_obj_tag(v___x_5486_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5486_, 1);
                    v___x_5487_ = crate::leanh::lean_box((v___x_5471_) as usize);
                    crate::leanh::lean_inc_ref(v_xh_5476_);
                    crate::leanh::lean_inc_ref(v_snd_5467_);
                    v___f_5488_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__8___boxed as *mut core::ffi::c_void,
                        19,
                        10,
                    );
                    crate::leanh::lean_closure_set(v___f_5488_, 0, v_a_5464_);
                    crate::leanh::lean_closure_set(v___f_5488_, 1, v_a_5465_);
                    crate::leanh::lean_closure_set(v___f_5488_, 2, v_u_5466_);
                    crate::leanh::lean_closure_set(v___f_5488_, 3, v_snd_5467_);
                    crate::leanh::lean_closure_set(v___f_5488_, 4, v___f_5468_);
                    crate::leanh::lean_closure_set(v___f_5488_, 5, v___x_5469_);
                    crate::leanh::lean_closure_set(v___f_5488_, 6, v_body_5470_);
                    crate::leanh::lean_closure_set(v___f_5488_, 7, v___x_5487_);
                    crate::leanh::lean_closure_set(v___f_5488_, 8, v___y_5472_);
                    crate::leanh::lean_closure_set(v___f_5488_, 9, v_xh_5476_);
                    if crate::leanh::lean_obj_tag(v_h_x3f_5474_) == 1 {
                        v_val_5500_ = crate::leanh::lean_ctor_get(v_h_x3f_5474_, 0);
                        crate::leanh::lean_inc(v_val_5500_);
                        crate::leanh::lean_dec_ref_known(v_h_x3f_5474_, 1);
                        v___x_5501_ = lean_array_get(v___x_5461_, v_xh_5476_, v___x_5475_);
                        crate::leanh::lean_dec_ref(v_xh_5476_);
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
                        if crate::leanh::lean_obj_tag(v___x_5502_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5502_, 1);
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
                            crate::leanh::lean_dec_ref(v___f_5488_);
                            crate::leanh::lean_dec(v_a_5473_);
                            crate::leanh::lean_dec_ref(v_snd_5467_);
                            v_a_5503_ = crate::leanh::lean_ctor_get(v___x_5502_, 0);
                            v_isSharedCheck_5510_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5502_)) as u8;
                            if v_isSharedCheck_5510_ == 0 {
                                v___x_5505_ = v___x_5502_;
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5503_);
                                crate::leanh::lean_dec(v___x_5502_);
                                v___x_5505_ = crate::leanh::lean_box(0);
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_xh_5476_);
                        crate::leanh::lean_dec(v_h_x3f_5474_);
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
                    crate::leanh::lean_dec_ref(v_xh_5476_);
                    crate::leanh::lean_dec(v_h_x3f_5474_);
                    crate::leanh::lean_dec(v_a_5473_);
                    crate::leanh::lean_dec(v___y_5472_);
                    crate::leanh::lean_dec(v_body_5470_);
                    crate::leanh::lean_dec(v___x_5469_);
                    crate::leanh::lean_dec_ref(v___f_5468_);
                    crate::leanh::lean_dec_ref(v_snd_5467_);
                    crate::leanh::lean_dec(v_u_5466_);
                    crate::leanh::lean_dec_ref(v_a_5465_);
                    crate::leanh::lean_dec_ref(v_a_5464_);
                    v_a_5511_ = crate::leanh::lean_ctor_get(v___x_5486_, 0);
                    v_isSharedCheck_5518_ = (!crate::leanh::lean_is_exclusive(v___x_5486_)) as u8;
                    if v_isSharedCheck_5518_ == 0 {
                        v___x_5513_ = v___x_5486_;
                        v_isShared_5514_ = v_isSharedCheck_5518_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5511_);
                        crate::leanh::lean_dec(v___x_5486_);
                        v___x_5513_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
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
                    v_reuseFailAlloc_5517_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5519_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5520_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_x_5521_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_5522_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_5523_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_u_5524_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_snd_5525_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_5526_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5527_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_body_5528_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5529_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5530_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_5531_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_h_x3f_5532_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_5533_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_xh_5534_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5535_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5536_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5537_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5538_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_5539_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_5540_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_5541_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_5542_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_72185__boxed_5543_: u8 = 0;
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_72185__boxed_5543_ = (crate::leanh::lean_unbox(v___x_5529_) as u8);
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
    crate::leanh::lean_dec(v___y_5541_);
    crate::leanh::lean_dec_ref(v___y_5540_);
    crate::leanh::lean_dec(v___y_5539_);
    crate::leanh::lean_dec_ref(v___y_5538_);
    crate::leanh::lean_dec(v___y_5537_);
    crate::leanh::lean_dec_ref(v___y_5536_);
    crate::leanh::lean_dec_ref(v___y_5535_);
    crate::leanh::lean_dec(v___x_5533_);
    crate::leanh::lean_dec(v___x_5520_);
    crate::leanh::lean_dec_ref(v___x_5519_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
    mut v_name_5545_: *mut crate::leanh::LeanObject,
    mut v_type_5546_: *mut crate::leanh::LeanObject,
    mut v_k_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5556_: u8 = 0;
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_name_5559_: *mut crate::leanh::LeanObject,
    mut v_type_5560_: *mut crate::leanh::LeanObject,
    mut v_k_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
    mut v___y_5563_: *mut crate::leanh::LeanObject,
    mut v___y_5564_: *mut crate::leanh::LeanObject,
    mut v___y_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5568_);
    crate::leanh::lean_dec_ref(v___y_5567_);
    crate::leanh::lean_dec(v___y_5566_);
    crate::leanh::lean_dec_ref(v___y_5565_);
    crate::leanh::lean_dec(v___y_5564_);
    crate::leanh::lean_dec_ref(v___y_5563_);
    crate::leanh::lean_dec_ref(v___y_5562_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__10(
    mut v_returnsEarly_5588_: u8,
    mut v_a_5589_: *mut crate::leanh::LeanObject,
    mut v_a_5590_: *mut crate::leanh::LeanObject,
    mut v_doBlockResultType_5591_: *mut crate::leanh::LeanObject,
    mut v_a_5592_: *mut crate::leanh::LeanObject,
    mut v_v_5593_: *mut crate::leanh::LeanObject,
    mut v_u_5594_: *mut crate::leanh::LeanObject,
    mut v___f_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___x_5597_: *mut crate::leanh::LeanObject,
    mut v___x_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ret_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: u8 = 0;
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_reuseFailAlloc_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_unused_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_returnsEarly_5588_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_5595_);
                    crate::leanh::lean_dec(v_u_5594_);
                    crate::leanh::lean_dec(v_v_5593_);
                    crate::leanh::lean_dec_ref(v_a_5592_);
                    crate::leanh::lean_dec_ref(v_doBlockResultType_5591_);
                    crate::leanh::lean_dec(v_a_5590_);
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
                    if crate::leanh::lean_obj_tag(v___x_5663_) == 0 {
                        v_a_5664_ = crate::leanh::lean_ctor_get(v___x_5663_, 0);
                        crate::leanh::lean_inc(v_a_5664_);
                        crate::leanh::lean_dec_ref_known(v___x_5663_, 1);
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
                            if crate::leanh::lean_obj_tag(v___x_5670_) == 0 {
                                v_a_5671_ = crate::leanh::lean_ctor_get(v___x_5670_, 0);
                                crate::leanh::lean_inc(v_a_5671_);
                                crate::leanh::lean_dec_ref_known(v___x_5670_, 1);
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
                                crate::leanh::lean_dec_ref(v___f_5595_);
                                crate::leanh::lean_dec(v_u_5594_);
                                crate::leanh::lean_dec(v_v_5593_);
                                crate::leanh::lean_dec_ref(v_a_5592_);
                                crate::leanh::lean_dec_ref(v_doBlockResultType_5591_);
                                crate::leanh::lean_dec_ref(v_a_5589_);
                                return v___x_5670_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_5595_);
                        crate::leanh::lean_dec(v_u_5594_);
                        crate::leanh::lean_dec(v_v_5593_);
                        crate::leanh::lean_dec_ref(v_a_5592_);
                        crate::leanh::lean_dec_ref(v_doBlockResultType_5591_);
                        crate::leanh::lean_dec_ref(v_a_5589_);
                        return v___x_5663_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5615_);
                crate::leanh::lean_inc_ref(v___y_5614_);
                crate::leanh::lean_inc(v___y_5613_);
                crate::leanh::lean_inc_ref(v___y_5612_);
                crate::leanh::lean_inc_ref(v_ret_5608_);
                v___x_5616_ = lean_infer_type(
                    v_ret_5608_,
                    v___y_5612_,
                    v___y_5613_,
                    v___y_5614_,
                    v___y_5615_,
                );
                if crate::leanh::lean_obj_tag(v___x_5616_) == 0 {
                    v_a_5617_ = crate::leanh::lean_ctor_get(v___x_5616_, 0);
                    crate::leanh::lean_inc(v_a_5617_);
                    crate::leanh::lean_dec_ref_known(v___x_5616_, 1);
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
                    if crate::leanh::lean_obj_tag(v___x_5618_) == 0 {
                        v_a_5619_ = crate::leanh::lean_ctor_get(v___x_5618_, 0);
                        crate::leanh::lean_inc(v_a_5619_);
                        crate::leanh::lean_dec_ref_known(v___x_5618_, 1);
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
                        if crate::leanh::lean_obj_tag(v___x_5620_) == 0 {
                            v_a_5621_ = crate::leanh::lean_ctor_get(v___x_5620_, 0);
                            crate::leanh::lean_inc(v_a_5621_);
                            crate::leanh::lean_dec_ref_known(v___x_5620_, 1);
                            v___x_5622_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__1;
                            v___x_5623_ =
                                l_Lean_Core_mkFreshUserName(v___x_5622_, v___y_5614_, v___y_5615_);
                            if crate::leanh::lean_obj_tag(v___x_5623_) == 0 {
                                v_a_5624_ = crate::leanh::lean_ctor_get(v___x_5623_, 0);
                                crate::leanh::lean_inc(v_a_5624_);
                                crate::leanh::lean_dec_ref_known(v___x_5623_, 1);
                                v_resultType_5625_ = crate::leanh::lean_ctor_get(v_a_5592_, 0);
                                v_isSharedCheck_5652_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_5592_)) as u8;
                                if v_isSharedCheck_5652_ == 0 {
                                    v_unused_5653_ = crate::leanh::lean_ctor_get(v_a_5592_, 1);
                                    crate::leanh::lean_dec(v_unused_5653_);
                                    v___x_5627_ = v_a_5592_;
                                    v_isShared_5628_ = v_isSharedCheck_5652_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_resultType_5625_);
                                    crate::leanh::lean_dec(v_a_5592_);
                                    v___x_5627_ = crate::leanh::lean_box(0);
                                    v_isShared_5628_ = v_isSharedCheck_5652_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5621_);
                                crate::leanh::lean_dec(v_a_5619_);
                                crate::leanh::lean_dec(v_a_5617_);
                                crate::leanh::lean_dec_ref(v_ret_5608_);
                                crate::leanh::lean_dec_ref(v___f_5595_);
                                crate::leanh::lean_dec(v_u_5594_);
                                crate::leanh::lean_dec(v_v_5593_);
                                crate::leanh::lean_dec_ref(v_a_5592_);
                                v_a_5654_ = crate::leanh::lean_ctor_get(v___x_5623_, 0);
                                v_isSharedCheck_5661_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5623_)) as u8;
                                if v_isSharedCheck_5661_ == 0 {
                                    v___x_5656_ = v___x_5623_;
                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5654_);
                                    crate::leanh::lean_dec(v___x_5623_);
                                    v___x_5656_ = crate::leanh::lean_box(0);
                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5619_);
                            crate::leanh::lean_dec(v_a_5617_);
                            crate::leanh::lean_dec_ref(v_ret_5608_);
                            crate::leanh::lean_dec_ref(v___f_5595_);
                            crate::leanh::lean_dec(v_u_5594_);
                            crate::leanh::lean_dec(v_v_5593_);
                            crate::leanh::lean_dec_ref(v_a_5592_);
                            return v___x_5620_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5617_);
                        crate::leanh::lean_dec_ref(v_ret_5608_);
                        crate::leanh::lean_dec_ref(v___f_5595_);
                        crate::leanh::lean_dec(v_u_5594_);
                        crate::leanh::lean_dec(v_v_5593_);
                        crate::leanh::lean_dec_ref(v_a_5592_);
                        crate::leanh::lean_dec_ref(v_a_5589_);
                        return v___x_5618_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ret_5608_);
                    crate::leanh::lean_dec_ref(v___f_5595_);
                    crate::leanh::lean_dec(v_u_5594_);
                    crate::leanh::lean_dec(v_v_5593_);
                    crate::leanh::lean_dec_ref(v_a_5592_);
                    crate::leanh::lean_dec_ref(v_doBlockResultType_5591_);
                    crate::leanh::lean_dec_ref(v_a_5589_);
                    return v___x_5616_;
                }
            }
            2 => {
                v___x_5629_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__2;
                v___x_5630_ = 0;
                v___x_5631_ = l_Lean_mkLambda(v___x_5629_, v___x_5630_, v_a_5617_, v_a_5619_);
                v___x_5632_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__6;
                v___x_5633_ = l_Lean_Level_succ___override(v_v_5593_);
                v___x_5634_ = crate::leanh::lean_box(0);
                if v_isShared_5628_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5627_, 1);
                    crate::leanh::lean_ctor_set(v___x_5627_, 1, v___x_5634_);
                    crate::leanh::lean_ctor_set(v___x_5627_, 0, v___x_5633_);
                    v___x_5636_ = v___x_5627_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___x_5634_);
                    v___x_5636_ = v_reuseFailAlloc_5651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5637_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5637_, 0, v_u_5594_);
                crate::leanh::lean_ctor_set(v___x_5637_, 1, v___x_5636_);
                v___x_5638_ = l_Lean_mkConst(v___x_5632_, v___x_5637_);
                crate::leanh::lean_inc_ref(v_resultType_5625_);
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
                if crate::leanh::lean_obj_tag(v___x_5640_) == 0 {
                    v_a_5641_ = crate::leanh::lean_ctor_get(v___x_5640_, 0);
                    v_isSharedCheck_5650_ = (!crate::leanh::lean_is_exclusive(v___x_5640_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v___x_5643_ = v___x_5640_;
                        v_isShared_5644_ = v_isSharedCheck_5650_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5641_);
                        crate::leanh::lean_dec(v___x_5640_);
                        v___x_5643_ = crate::leanh::lean_box(0);
                        v_isShared_5644_ = v_isSharedCheck_5650_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5639_);
                    crate::leanh::lean_dec(v_a_5621_);
                    return v___x_5640_;
                }
            }
            4 => {
                v___x_5645_ = l_Lean_mkSimpleThunk(v_a_5621_);
                v___x_5646_ = l_Lean_mkAppB(v___x_5639_, v_a_5641_, v___x_5645_);
                if v_isShared_5644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5643_, 0, v___x_5646_);
                    v___x_5648_ = v___x_5643_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
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
                    v_reuseFailAlloc_5660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_returnsEarly_5672_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_5673_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_5674_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_doBlockResultType_5675_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_5676_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_v_5677_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_u_5678_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_5679_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5680_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5681_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5682_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5683_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5684_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5685_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5686_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5687_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5688_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5689_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5690_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_returnsEarly_boxed_5691_: u8 = 0;
    let mut v_res_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_returnsEarly_boxed_5691_ = (crate::leanh::lean_unbox(v_returnsEarly_5672_) as u8);
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
    crate::leanh::lean_dec(v___y_5689_);
    crate::leanh::lean_dec_ref(v___y_5688_);
    crate::leanh::lean_dec(v___y_5687_);
    crate::leanh::lean_dec_ref(v___y_5686_);
    crate::leanh::lean_dec(v___y_5685_);
    crate::leanh::lean_dec_ref(v___y_5684_);
    crate::leanh::lean_dec_ref(v___y_5683_);
    crate::leanh::lean_dec(v___x_5682_);
    crate::leanh::lean_dec(v___x_5681_);
    crate::leanh::lean_dec_ref(v___y_5680_);
    return v_res_5692_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__11(
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
    mut v___x_5695_: *mut crate::leanh::LeanObject,
    mut v___x_5696_: u8,
    mut v_postS_5697_: *mut crate::leanh::LeanObject,
    mut v___y_5698_: *mut crate::leanh::LeanObject,
    mut v___y_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
    mut v___y_5702_: *mut crate::leanh::LeanObject,
    mut v___y_5703_: *mut crate::leanh::LeanObject,
    mut v___y_5704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    if crate::leanh::lean_obj_tag(v___x_5707_) == 0 {
        let mut v_a_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5711_: u8 = 0;
        let mut v___x_5712_: u8 = 0;
        let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5708_ = crate::leanh::lean_ctor_get(v___x_5707_, 0);
        crate::leanh::lean_inc(v_a_5708_);
        crate::leanh::lean_dec_ref_known(v___x_5707_, 1);
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
        crate::leanh::lean_dec_ref(v___x_5710_);
        return v___x_5713_;
    } else {
        crate::leanh::lean_dec_ref(v_postS_5697_);
        return v___x_5707_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__11___boxed(
    mut v___y_5714_: *mut crate::leanh::LeanObject,
    mut v___y_5715_: *mut crate::leanh::LeanObject,
    mut v___x_5716_: *mut crate::leanh::LeanObject,
    mut v___x_5717_: *mut crate::leanh::LeanObject,
    mut v_postS_5718_: *mut crate::leanh::LeanObject,
    mut v___y_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
    mut v___y_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_72567__boxed_5727_: u8 = 0;
    let mut v_res_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_72567__boxed_5727_ = (crate::leanh::lean_unbox(v___x_5717_) as u8);
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
    crate::leanh::lean_dec(v___y_5725_);
    crate::leanh::lean_dec_ref(v___y_5724_);
    crate::leanh::lean_dec(v___y_5723_);
    crate::leanh::lean_dec_ref(v___y_5722_);
    crate::leanh::lean_dec(v___y_5721_);
    crate::leanh::lean_dec_ref(v___y_5720_);
    crate::leanh::lean_dec_ref(v___y_5719_);
    crate::leanh::lean_dec(v___x_5716_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__12(
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
    mut v___x_5736_: *mut crate::leanh::LeanObject,
    mut v_a_5737_: *mut crate::leanh::LeanObject,
    mut v_a_5738_: *mut crate::leanh::LeanObject,
    mut v_val_5739_: *mut crate::leanh::LeanObject,
    mut v_a_5740_: *mut crate::leanh::LeanObject,
    mut v_x_5741_: *mut crate::leanh::LeanObject,
    mut v___y_5742_: *mut crate::leanh::LeanObject,
    mut v___y_5743_: *mut crate::leanh::LeanObject,
    mut v___y_5744_: *mut crate::leanh::LeanObject,
    mut v___y_5745_: *mut crate::leanh::LeanObject,
    mut v___y_5746_: *mut crate::leanh::LeanObject,
    mut v___y_5747_: *mut crate::leanh::LeanObject,
    mut v___y_5748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_Elab_Do_elabDoFor___lam__12___closed__2;
    v___x_5751_ = crate::leanh::lean_box(0);
    v___x_5752_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5752_, 0, v_a_5734_);
    crate::leanh::lean_ctor_set(v___x_5752_, 1, v___x_5751_);
    v___x_5753_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5753_, 0, v_a_5735_);
    crate::leanh::lean_ctor_set(v___x_5753_, 1, v___x_5752_);
    v___x_5754_ = l_Lean_mkConst(v___x_5750_, v___x_5753_);
    v___x_5755_ = l_Lean_instInhabitedExpr;
    v___x_5756_ = lean_array_get_borrowed(v___x_5755_, v_x_5741_, v___x_5736_);
    crate::leanh::lean_inc(v___x_5756_);
    v___x_5757_ = l_Lean_mkApp5(
        v___x_5754_,
        v_a_5737_,
        v_a_5738_,
        v_val_5739_,
        v_a_5740_,
        v___x_5756_,
    );
    v___x_5758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__12___boxed(
    mut v_a_5759_: *mut crate::leanh::LeanObject,
    mut v_a_5760_: *mut crate::leanh::LeanObject,
    mut v___x_5761_: *mut crate::leanh::LeanObject,
    mut v_a_5762_: *mut crate::leanh::LeanObject,
    mut v_a_5763_: *mut crate::leanh::LeanObject,
    mut v_val_5764_: *mut crate::leanh::LeanObject,
    mut v_a_5765_: *mut crate::leanh::LeanObject,
    mut v_x_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
    mut v___y_5768_: *mut crate::leanh::LeanObject,
    mut v___y_5769_: *mut crate::leanh::LeanObject,
    mut v___y_5770_: *mut crate::leanh::LeanObject,
    mut v___y_5771_: *mut crate::leanh::LeanObject,
    mut v___y_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5773_);
    crate::leanh::lean_dec_ref(v___y_5772_);
    crate::leanh::lean_dec(v___y_5771_);
    crate::leanh::lean_dec_ref(v___y_5770_);
    crate::leanh::lean_dec(v___y_5769_);
    crate::leanh::lean_dec_ref(v___y_5768_);
    crate::leanh::lean_dec_ref(v___y_5767_);
    crate::leanh::lean_dec_ref(v_x_5766_);
    crate::leanh::lean_dec(v___x_5761_);
    return v_res_5775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(
    mut v_a_5776_: *mut crate::leanh::LeanObject,
    mut v_as_5777_: *mut crate::leanh::LeanObject,
    mut v_i_5778_: usize,
    mut v_stop_5779_: usize,
    mut v_b_5780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5786_: u8 = 0;
    let mut v_reassigns_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5786_ = lean_usize_dec_eq(v_i_5778_, v_stop_5779_);
                if v___x_5786_ == 0 {
                    v_reassigns_5787_ = crate::leanh::lean_ctor_get(v_a_5776_, 1);
                    v___x_5788_ = lean_array_uget_borrowed(v_as_5777_, v_i_5778_);
                    v___x_5789_ = l_Lean_TSyntax_getId(v___x_5788_);
                    v___x_5790_ = l_Lean_NameSet_contains(v_reassigns_5787_, v___x_5789_);
                    crate::leanh::lean_dec(v___x_5789_);
                    if v___x_5790_ == 0 {
                        v___y_5782_ = v_b_5780_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_5788_);
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
    mut v_a_5792_: *mut crate::leanh::LeanObject,
    mut v_as_5793_: *mut crate::leanh::LeanObject,
    mut v_i_5794_: *mut crate::leanh::LeanObject,
    mut v_stop_5795_: *mut crate::leanh::LeanObject,
    mut v_b_5796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5797_: usize = 0;
    let mut v_stop_boxed_5798_: usize = 0;
    let mut v_res_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5797_ = crate::leanh::lean_unbox_usize(v_i_5794_);
    crate::leanh::lean_dec(v_i_5794_);
    v_stop_boxed_5798_ = crate::leanh::lean_unbox_usize(v_stop_5795_);
    crate::leanh::lean_dec(v_stop_5795_);
    v_res_5799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_5792_, v_as_5793_, v_i_boxed_5797_, v_stop_boxed_5798_, v_b_5796_);
    crate::leanh::lean_dec_ref(v_as_5793_);
    crate::leanh::lean_dec_ref(v_a_5792_);
    return v_res_5799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(
    mut v_sz_5800_: usize,
    mut v_i_5801_: usize,
    mut v_bs_5802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5803_: u8 = 0;
    let mut v_v_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: usize = 0;
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5803_ = lean_usize_dec_lt(v_i_5801_, v_sz_5800_);
                if v___x_5803_ == 0 {
                    return v_bs_5802_;
                } else {
                    v_v_5804_ = lean_array_uget(v_bs_5802_, v_i_5801_);
                    v___x_5805_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5806_ = lean_array_uset(v_bs_5802_, v_i_5801_, v___x_5805_);
                    v___x_5807_ = l_Lean_TSyntax_getId(v_v_5804_);
                    crate::leanh::lean_dec(v_v_5804_);
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
    mut v_sz_5812_: *mut crate::leanh::LeanObject,
    mut v_i_5813_: *mut crate::leanh::LeanObject,
    mut v_bs_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5815_: usize = 0;
    let mut v_i_boxed_5816_: usize = 0;
    let mut v_res_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5815_ = crate::leanh::lean_unbox_usize(v_sz_5812_);
    crate::leanh::lean_dec(v_sz_5812_);
    v_i_boxed_5816_ = crate::leanh::lean_unbox_usize(v_i_5813_);
    crate::leanh::lean_dec(v_i_5813_);
    v_res_5817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_boxed_5815_, v_i_boxed_5816_, v_bs_5814_);
    return v_res_5817_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(
    mut v___x_5818_: *mut crate::leanh::LeanObject,
    mut v_a_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
    mut v___y_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70870__overap_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_instInhabitedExpr;
    v___x_70870__overap_5829_ = l_instInhabitedOfMonad___redArg(v___x_5818_, v___x_5828_);
    crate::leanh::lean_inc(v___y_5826_);
    crate::leanh::lean_inc_ref(v___y_5825_);
    crate::leanh::lean_inc(v___y_5824_);
    crate::leanh::lean_inc_ref(v___y_5823_);
    crate::leanh::lean_inc(v___y_5822_);
    crate::leanh::lean_inc_ref(v___y_5821_);
    crate::leanh::lean_inc_ref(v___y_5820_);
    v___x_5830_ = crate::leanh::lean_apply_8(
        v___x_70870__overap_5829_,
        v___y_5820_,
        v___y_5821_,
        v___y_5822_,
        v___y_5823_,
        v___y_5824_,
        v___y_5825_,
        v___y_5826_,
        crate::leanh::lean_box(0),
    );
    return v___x_5830_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(
    mut v___x_5831_: *mut crate::leanh::LeanObject,
    mut v_a_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5841_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_5831_, v_a_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
    crate::leanh::lean_dec(v___y_5839_);
    crate::leanh::lean_dec_ref(v___y_5838_);
    crate::leanh::lean_dec(v___y_5837_);
    crate::leanh::lean_dec_ref(v___y_5836_);
    crate::leanh::lean_dec(v___y_5835_);
    crate::leanh::lean_dec_ref(v___y_5834_);
    crate::leanh::lean_dec_ref(v___y_5833_);
    crate::leanh::lean_dec_ref(v_a_5832_);
    return v_res_5841_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5842_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5842_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
    v___x_5844_ = l_StateRefT_x27_instMonad___redArg(v___x_5843_);
    return v___x_5844_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(
    mut v_acc_5851_: *mut crate::leanh::LeanObject,
    mut v_declInfos_5852_: *mut crate::leanh::LeanObject,
    mut v_k_5853_: *mut crate::leanh::LeanObject,
    mut v_kind_5854_: *mut crate::leanh::LeanObject,
    mut v_x_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
    mut v___y_5858_: *mut crate::leanh::LeanObject,
    mut v___y_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5864_: u8 = 0;
    let mut v_res_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5864_ = (crate::leanh::lean_unbox(v_kind_5854_) as u8);
    v_res_5865_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_5851_, v_declInfos_5852_, v_k_5853_, v_kind_boxed_5864_, v_x_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
    crate::leanh::lean_dec(v___y_5862_);
    crate::leanh::lean_dec_ref(v___y_5861_);
    crate::leanh::lean_dec(v___y_5860_);
    crate::leanh::lean_dec_ref(v___y_5859_);
    crate::leanh::lean_dec(v___y_5858_);
    crate::leanh::lean_dec_ref(v___y_5857_);
    crate::leanh::lean_dec_ref(v___y_5856_);
    return v_res_5865_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(
    mut v_declInfos_5866_: *mut crate::leanh::LeanObject,
    mut v_k_5867_: *mut crate::leanh::LeanObject,
    mut v_kind_5868_: u8,
    mut v_acc_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v_toFunctor_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___f_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v_toFunctor_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5929_: u8 = 0;
    let mut v___f_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: u8 = 0;
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___f_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut v_unused_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5969_: u8 = 0;
    let mut v_unused_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_unused_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_unused_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5878_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
                v_toApplicative_5879_ = crate::leanh::lean_ctor_get(v___x_5878_, 0);
                v_toFunctor_5880_ = crate::leanh::lean_ctor_get(v_toApplicative_5879_, 0);
                v_toSeq_5881_ = crate::leanh::lean_ctor_get(v_toApplicative_5879_, 2);
                v_toSeqLeft_5882_ = crate::leanh::lean_ctor_get(v_toApplicative_5879_, 3);
                v_toSeqRight_5883_ = crate::leanh::lean_ctor_get(v_toApplicative_5879_, 4);
                v___f_5884_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2;
                v___f_5885_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_5880_, 2);
                v___f_5886_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5886_, 0, v_toFunctor_5880_);
                v___f_5887_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5887_, 0, v_toFunctor_5880_);
                v___x_5888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5888_, 0, v___f_5886_);
                crate::leanh::lean_ctor_set(v___x_5888_, 1, v___f_5887_);
                crate::leanh::lean_inc(v_toSeqRight_5883_);
                v___f_5889_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5889_, 0, v_toSeqRight_5883_);
                crate::leanh::lean_inc(v_toSeqLeft_5882_);
                v___f_5890_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5890_, 0, v_toSeqLeft_5882_);
                crate::leanh::lean_inc(v_toSeq_5881_);
                v___f_5891_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5891_, 0, v_toSeq_5881_);
                v___x_5892_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5892_, 0, v___x_5888_);
                crate::leanh::lean_ctor_set(v___x_5892_, 1, v___f_5884_);
                crate::leanh::lean_ctor_set(v___x_5892_, 2, v___f_5891_);
                crate::leanh::lean_ctor_set(v___x_5892_, 3, v___f_5890_);
                crate::leanh::lean_ctor_set(v___x_5892_, 4, v___f_5889_);
                v___x_5893_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5893_, 0, v___x_5892_);
                crate::leanh::lean_ctor_set(v___x_5893_, 1, v___f_5885_);
                v___x_5894_ = l_StateRefT_x27_instMonad___redArg(v___x_5893_);
                v_toApplicative_5895_ = crate::leanh::lean_ctor_get(v___x_5894_, 0);
                v_isSharedCheck_5975_ = (!crate::leanh::lean_is_exclusive(v___x_5894_)) as u8;
                if v_isSharedCheck_5975_ == 0 {
                    v_unused_5976_ = crate::leanh::lean_ctor_get(v___x_5894_, 1);
                    crate::leanh::lean_dec(v_unused_5976_);
                    v___x_5897_ = v___x_5894_;
                    v_isShared_5898_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5895_);
                    crate::leanh::lean_dec(v___x_5894_);
                    v___x_5897_ = crate::leanh::lean_box(0);
                    v_isShared_5898_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5899_ = crate::leanh::lean_ctor_get(v_toApplicative_5895_, 0);
                v_toSeq_5900_ = crate::leanh::lean_ctor_get(v_toApplicative_5895_, 2);
                v_toSeqLeft_5901_ = crate::leanh::lean_ctor_get(v_toApplicative_5895_, 3);
                v_toSeqRight_5902_ = crate::leanh::lean_ctor_get(v_toApplicative_5895_, 4);
                v_isSharedCheck_5973_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5895_)) as u8;
                if v_isSharedCheck_5973_ == 0 {
                    v_unused_5974_ = crate::leanh::lean_ctor_get(v_toApplicative_5895_, 1);
                    crate::leanh::lean_dec(v_unused_5974_);
                    v___x_5904_ = v_toApplicative_5895_;
                    v_isShared_5905_ = v_isSharedCheck_5973_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5902_);
                    crate::leanh::lean_inc(v_toSeqLeft_5901_);
                    crate::leanh::lean_inc(v_toSeq_5900_);
                    crate::leanh::lean_inc(v_toFunctor_5899_);
                    crate::leanh::lean_dec(v_toApplicative_5895_);
                    v___x_5904_ = crate::leanh::lean_box(0);
                    v_isShared_5905_ = v_isSharedCheck_5973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4;
                v___f_5907_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_5899_);
                v___f_5908_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5908_, 0, v_toFunctor_5899_);
                v___f_5909_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5909_, 0, v_toFunctor_5899_);
                v___x_5910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5910_, 0, v___f_5908_);
                crate::leanh::lean_ctor_set(v___x_5910_, 1, v___f_5909_);
                v___f_5911_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5911_, 0, v_toSeqRight_5902_);
                v___f_5912_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5912_, 0, v_toSeqLeft_5901_);
                v___f_5913_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5913_, 0, v_toSeq_5900_);
                if v_isShared_5905_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5904_, 4, v___f_5911_);
                    crate::leanh::lean_ctor_set(v___x_5904_, 3, v___f_5912_);
                    crate::leanh::lean_ctor_set(v___x_5904_, 2, v___f_5913_);
                    crate::leanh::lean_ctor_set(v___x_5904_, 1, v___f_5906_);
                    crate::leanh::lean_ctor_set(v___x_5904_, 0, v___x_5910_);
                    v___x_5915_ = v___x_5904_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5972_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___f_5906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 2, v___f_5913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 3, v___f_5912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 4, v___f_5911_);
                    v___x_5915_ = v_reuseFailAlloc_5972_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5897_, 1, v___f_5907_);
                    crate::leanh::lean_ctor_set(v___x_5897_, 0, v___x_5915_);
                    v___x_5917_ = v___x_5897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___f_5907_);
                    v___x_5917_ = v_reuseFailAlloc_5971_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5918_ = l_StateRefT_x27_instMonad___redArg(v___x_5917_);
                v_toApplicative_5919_ = crate::leanh::lean_ctor_get(v___x_5918_, 0);
                v_isSharedCheck_5969_ = (!crate::leanh::lean_is_exclusive(v___x_5918_)) as u8;
                if v_isSharedCheck_5969_ == 0 {
                    v_unused_5970_ = crate::leanh::lean_ctor_get(v___x_5918_, 1);
                    crate::leanh::lean_dec(v_unused_5970_);
                    v___x_5921_ = v___x_5918_;
                    v_isShared_5922_ = v_isSharedCheck_5969_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5919_);
                    crate::leanh::lean_dec(v___x_5918_);
                    v___x_5921_ = crate::leanh::lean_box(0);
                    v_isShared_5922_ = v_isSharedCheck_5969_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5923_ = crate::leanh::lean_ctor_get(v_toApplicative_5919_, 0);
                v_toSeq_5924_ = crate::leanh::lean_ctor_get(v_toApplicative_5919_, 2);
                v_toSeqLeft_5925_ = crate::leanh::lean_ctor_get(v_toApplicative_5919_, 3);
                v_toSeqRight_5926_ = crate::leanh::lean_ctor_get(v_toApplicative_5919_, 4);
                v_isSharedCheck_5967_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5919_)) as u8;
                if v_isSharedCheck_5967_ == 0 {
                    v_unused_5968_ = crate::leanh::lean_ctor_get(v_toApplicative_5919_, 1);
                    crate::leanh::lean_dec(v_unused_5968_);
                    v___x_5928_ = v_toApplicative_5919_;
                    v_isShared_5929_ = v_isSharedCheck_5967_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5926_);
                    crate::leanh::lean_inc(v_toSeqLeft_5925_);
                    crate::leanh::lean_inc(v_toSeq_5924_);
                    crate::leanh::lean_inc(v_toFunctor_5923_);
                    crate::leanh::lean_dec(v_toApplicative_5919_);
                    v___x_5928_ = crate::leanh::lean_box(0);
                    v_isShared_5929_ = v_isSharedCheck_5967_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6;
                v___f_5931_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7;
                crate::leanh::lean_inc_ref(v_toFunctor_5923_);
                v___f_5932_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5932_, 0, v_toFunctor_5923_);
                v___f_5933_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5933_, 0, v_toFunctor_5923_);
                v___x_5934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5934_, 0, v___f_5932_);
                crate::leanh::lean_ctor_set(v___x_5934_, 1, v___f_5933_);
                v___f_5935_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5935_, 0, v_toSeqRight_5926_);
                v___f_5936_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5936_, 0, v_toSeqLeft_5925_);
                v___f_5937_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5937_, 0, v_toSeq_5924_);
                if v_isShared_5929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5928_, 4, v___f_5935_);
                    crate::leanh::lean_ctor_set(v___x_5928_, 3, v___f_5936_);
                    crate::leanh::lean_ctor_set(v___x_5928_, 2, v___f_5937_);
                    crate::leanh::lean_ctor_set(v___x_5928_, 1, v___f_5930_);
                    crate::leanh::lean_ctor_set(v___x_5928_, 0, v___x_5934_);
                    v___x_5939_ = v___x_5928_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5966_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 1, v___f_5930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 2, v___f_5937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 3, v___f_5936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 4, v___f_5935_);
                    v___x_5939_ = v_reuseFailAlloc_5966_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 1, v___f_5931_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_5939_);
                    v___x_5941_ = v___x_5921_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 0, v___x_5939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 1, v___f_5931_);
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
                    crate::leanh::lean_dec_ref(v___x_5942_);
                    crate::leanh::lean_dec_ref(v_declInfos_5866_);
                    crate::leanh::lean_inc(v___y_5876_);
                    crate::leanh::lean_inc_ref(v___y_5875_);
                    crate::leanh::lean_inc(v___y_5874_);
                    crate::leanh::lean_inc_ref(v___y_5873_);
                    crate::leanh::lean_inc(v___y_5872_);
                    crate::leanh::lean_inc_ref(v___y_5871_);
                    crate::leanh::lean_inc_ref(v___y_5870_);
                    v___x_5946_ = crate::leanh::lean_apply_9(
                        v_k_5867_,
                        v_acc_5869_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                        v___y_5874_,
                        v___y_5875_,
                        v___y_5876_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5946_;
                } else {
                    v___f_5947_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                    crate::leanh::lean_closure_set(v___f_5947_, 0, v___x_5942_);
                    v___x_5948_ = crate::leanh::lean_box(0);
                    v___x_5949_ = 0;
                    v___f_5950_ = crate::leanh::lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5950_, 0, v___f_5947_);
                    v___x_5951_ = crate::leanh::lean_box((v___x_5949_) as usize);
                    v___x_5952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5952_, 0, v___x_5951_);
                    crate::leanh::lean_ctor_set(v___x_5952_, 1, v___f_5950_);
                    v___x_5953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5953_, 0, v___x_5948_);
                    crate::leanh::lean_ctor_set(v___x_5953_, 1, v___x_5952_);
                    v___x_5954_ = lean_array_get(v___x_5953_, v_declInfos_5866_, v___x_5943_);
                    crate::leanh::lean_dec_ref_known(v___x_5953_, 2);
                    v_snd_5955_ = crate::leanh::lean_ctor_get(v___x_5954_, 1);
                    crate::leanh::lean_inc(v_snd_5955_);
                    v_fst_5956_ = crate::leanh::lean_ctor_get(v___x_5954_, 0);
                    crate::leanh::lean_inc(v_fst_5956_);
                    crate::leanh::lean_dec(v___x_5954_);
                    v_fst_5957_ = crate::leanh::lean_ctor_get(v_snd_5955_, 0);
                    crate::leanh::lean_inc(v_fst_5957_);
                    v_snd_5958_ = crate::leanh::lean_ctor_get(v_snd_5955_, 1);
                    crate::leanh::lean_inc(v_snd_5958_);
                    crate::leanh::lean_dec(v_snd_5955_);
                    crate::leanh::lean_inc(v___y_5876_);
                    crate::leanh::lean_inc_ref(v___y_5875_);
                    crate::leanh::lean_inc(v___y_5874_);
                    crate::leanh::lean_inc_ref(v___y_5873_);
                    crate::leanh::lean_inc(v___y_5872_);
                    crate::leanh::lean_inc_ref(v___y_5871_);
                    crate::leanh::lean_inc_ref(v___y_5870_);
                    crate::leanh::lean_inc_ref(v_acc_5869_);
                    v___x_5959_ = crate::leanh::lean_apply_9(
                        v_snd_5958_,
                        v_acc_5869_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                        v___y_5874_,
                        v___y_5875_,
                        v___y_5876_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5959_) == 0 {
                        v_a_5960_ = crate::leanh::lean_ctor_get(v___x_5959_, 0);
                        crate::leanh::lean_inc(v_a_5960_);
                        crate::leanh::lean_dec_ref_known(v___x_5959_, 1);
                        v___x_5961_ = crate::leanh::lean_box((v_kind_5868_) as usize);
                        v___f_5962_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed as *mut core::ffi::c_void, 13, 4);
                        crate::leanh::lean_closure_set(v___f_5962_, 0, v_acc_5869_);
                        crate::leanh::lean_closure_set(v___f_5962_, 1, v_declInfos_5866_);
                        crate::leanh::lean_closure_set(v___f_5962_, 2, v_k_5867_);
                        crate::leanh::lean_closure_set(v___f_5962_, 3, v___x_5961_);
                        v___x_5963_ = (crate::leanh::lean_unbox(v_fst_5957_) as u8);
                        crate::leanh::lean_dec(v_fst_5957_);
                        v___x_5964_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_5956_, v___x_5963_, v_a_5960_, v___f_5962_, v_kind_5868_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                        return v___x_5964_;
                    } else {
                        crate::leanh::lean_dec(v_fst_5957_);
                        crate::leanh::lean_dec(v_fst_5956_);
                        crate::leanh::lean_dec_ref(v_acc_5869_);
                        crate::leanh::lean_dec_ref(v_k_5867_);
                        crate::leanh::lean_dec_ref(v_declInfos_5866_);
                        return v___x_5959_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(
    mut v_acc_5977_: *mut crate::leanh::LeanObject,
    mut v_declInfos_5978_: *mut crate::leanh::LeanObject,
    mut v_k_5979_: *mut crate::leanh::LeanObject,
    mut v_kind_5980_: u8,
    mut v_x_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
    mut v___y_5985_: *mut crate::leanh::LeanObject,
    mut v___y_5986_: *mut crate::leanh::LeanObject,
    mut v___y_5987_: *mut crate::leanh::LeanObject,
    mut v___y_5988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5990_ = lean_array_push(v_acc_5977_, v_x_5981_);
    v___x_5991_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_5978_, v_k_5979_, v_kind_5980_, v___x_5990_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_);
    return v___x_5991_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(
    mut v_declInfos_5992_: *mut crate::leanh::LeanObject,
    mut v_k_5993_: *mut crate::leanh::LeanObject,
    mut v_kind_5994_: *mut crate::leanh::LeanObject,
    mut v_acc_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6004_: u8 = 0;
    let mut v_res_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6004_ = (crate::leanh::lean_unbox(v_kind_5994_) as u8);
    v_res_6005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_5992_, v_k_5993_, v_kind_boxed_6004_, v_acc_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
    crate::leanh::lean_dec(v___y_6002_);
    crate::leanh::lean_dec_ref(v___y_6001_);
    crate::leanh::lean_dec(v___y_6000_);
    crate::leanh::lean_dec_ref(v___y_5999_);
    crate::leanh::lean_dec(v___y_5998_);
    crate::leanh::lean_dec_ref(v___y_5997_);
    crate::leanh::lean_dec_ref(v___y_5996_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(
    mut v_declInfos_6008_: *mut crate::leanh::LeanObject,
    mut v_k_6009_: *mut crate::leanh::LeanObject,
    mut v_kind_6010_: u8,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
    mut v___y_6012_: *mut crate::leanh::LeanObject,
    mut v___y_6013_: *mut crate::leanh::LeanObject,
    mut v___y_6014_: *mut crate::leanh::LeanObject,
    mut v___y_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6019_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0;
    v___x_6020_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_6008_, v_k_6009_, v_kind_6010_, v___x_6019_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_);
    return v___x_6020_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(
    mut v_declInfos_6021_: *mut crate::leanh::LeanObject,
    mut v_k_6022_: *mut crate::leanh::LeanObject,
    mut v_kind_6023_: *mut crate::leanh::LeanObject,
    mut v___y_6024_: *mut crate::leanh::LeanObject,
    mut v___y_6025_: *mut crate::leanh::LeanObject,
    mut v___y_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
    mut v___y_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6032_: u8 = 0;
    let mut v_res_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6032_ = (crate::leanh::lean_unbox(v_kind_6023_) as u8);
    v_res_6033_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_6021_, v_k_6022_, v_kind_boxed_6032_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_);
    crate::leanh::lean_dec(v___y_6030_);
    crate::leanh::lean_dec_ref(v___y_6029_);
    crate::leanh::lean_dec(v___y_6028_);
    crate::leanh::lean_dec_ref(v___y_6027_);
    crate::leanh::lean_dec(v___y_6026_);
    crate::leanh::lean_dec_ref(v___y_6025_);
    crate::leanh::lean_dec_ref(v___y_6024_);
    return v_res_6033_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(
    mut v_sz_6034_: usize,
    mut v_i_6035_: usize,
    mut v_bs_6036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6037_: u8 = 0;
    let mut v_v_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: usize = 0;
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v_fst_6039_ = crate::leanh::lean_ctor_get(v_v_6038_, 0);
                    v_snd_6040_ = crate::leanh::lean_ctor_get(v_v_6038_, 1);
                    v_isSharedCheck_6056_ = (!crate::leanh::lean_is_exclusive(v_v_6038_)) as u8;
                    if v_isSharedCheck_6056_ == 0 {
                        v___x_6042_ = v_v_6038_;
                        v_isShared_6043_ = v_isSharedCheck_6056_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6040_);
                        crate::leanh::lean_inc(v_fst_6039_);
                        crate::leanh::lean_dec(v_v_6038_);
                        v___x_6042_ = crate::leanh::lean_box(0);
                        v_isShared_6043_ = v_isSharedCheck_6056_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6044_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_6045_ = lean_array_uset(v_bs_6036_, v_i_6035_, v___x_6044_);
                v___x_6046_ = 0;
                v___x_6047_ = crate::leanh::lean_box((v___x_6046_) as usize);
                if v_isShared_6043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6042_, 0, v___x_6047_);
                    v___x_6049_ = v___x_6042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 1, v_snd_6040_);
                    v___x_6049_ = v_reuseFailAlloc_6055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6050_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6050_, 0, v_fst_6039_);
                crate::leanh::lean_ctor_set(v___x_6050_, 1, v___x_6049_);
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
    mut v_sz_6057_: *mut crate::leanh::LeanObject,
    mut v_i_6058_: *mut crate::leanh::LeanObject,
    mut v_bs_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6060_: usize = 0;
    let mut v_i_boxed_6061_: usize = 0;
    let mut v_res_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6060_ = crate::leanh::lean_unbox_usize(v_sz_6057_);
    crate::leanh::lean_dec(v_sz_6057_);
    v_i_boxed_6061_ = crate::leanh::lean_unbox_usize(v_i_6058_);
    crate::leanh::lean_dec(v_i_6058_);
    v_res_6062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_6060_, v_i_boxed_6061_, v_bs_6059_);
    return v_res_6062_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(
    mut v_declInfos_6063_: *mut crate::leanh::LeanObject,
    mut v_k_6064_: *mut crate::leanh::LeanObject,
    mut v_kind_6065_: u8,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
    mut v___y_6068_: *mut crate::leanh::LeanObject,
    mut v___y_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_6074_: usize = 0;
    let mut v___x_6075_: usize = 0;
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_6074_ = lean_array_size(v_declInfos_6063_);
    v___x_6075_ = 0usize;
    v___x_6076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_6074_, v___x_6075_, v_declInfos_6063_);
    v___x_6077_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_6076_, v_k_6064_, v_kind_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
    return v___x_6077_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(
    mut v_declInfos_6078_: *mut crate::leanh::LeanObject,
    mut v_k_6079_: *mut crate::leanh::LeanObject,
    mut v_kind_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
    mut v___y_6082_: *mut crate::leanh::LeanObject,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
    mut v___y_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6089_: u8 = 0;
    let mut v_res_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6089_ = (crate::leanh::lean_unbox(v_kind_6080_) as u8);
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
    crate::leanh::lean_dec(v___y_6087_);
    crate::leanh::lean_dec_ref(v___y_6086_);
    crate::leanh::lean_dec(v___y_6085_);
    crate::leanh::lean_dec_ref(v___y_6084_);
    crate::leanh::lean_dec(v___y_6083_);
    crate::leanh::lean_dec_ref(v___y_6082_);
    crate::leanh::lean_dec_ref(v___y_6081_);
    return v_res_6090_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor(
    mut v_stx_6119_: *mut crate::leanh::LeanObject,
    mut v_dec_6120_: *mut crate::leanh::LeanObject,
    mut v_a_6121_: *mut crate::leanh::LeanObject,
    mut v_a_6122_: *mut crate::leanh::LeanObject,
    mut v_a_6123_: *mut crate::leanh::LeanObject,
    mut v_a_6124_: *mut crate::leanh::LeanObject,
    mut v_a_6125_: *mut crate::leanh::LeanObject,
    mut v_a_6126_: *mut crate::leanh::LeanObject,
    mut v_a_6127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: u8 = 0;
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: u8 = 0;
    let mut v___y_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: u8 = 0;
    let mut v___y_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: u8 = 0;
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6188_: u8 = 0;
    let mut v___y_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6237_: u8 = 0;
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6241_: u8 = 0;
    let mut v___y_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6248_: u8 = 0;
    let mut v___y_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6270_: u8 = 0;
    let mut v___y_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6289_: u8 = 0;
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6305_: u8 = 0;
    let mut v_fst_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_reuseFailAlloc_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut v_a_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6346_: u8 = 0;
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut v_a_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut v___y_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6371_: u8 = 0;
    let mut v___y_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6388_: u8 = 0;
    let mut v___y_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_returnsEarly_6394_: u8 = 0;
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6398_: usize = 0;
    let mut v___x_6399_: usize = 0;
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6402_: usize = 0;
    let mut v___x_6403_: usize = 0;
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: u8 = 0;
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6440_: u8 = 0;
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVars_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u8 = 0;
    let mut v___x_6475_: u8 = 0;
    let mut v___x_6476_: usize = 0;
    let mut v___x_6477_: usize = 0;
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: usize = 0;
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v_a_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6497_: u8 = 0;
    let mut v_a_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6501_: u8 = 0;
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v_reuseFailAlloc_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_reuseFailAlloc_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut v_a_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6513_: u8 = 0;
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6517_: u8 = 0;
    let mut v_a_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6525_: u8 = 0;
    let mut v_a_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut v_a_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: u8 = 0;
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: u8 = 0;
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6129_ = l_Lean_Elab_Do_expandDoFor___closed__1;
                crate::leanh::lean_inc(v_stx_6119_);
                v___x_6130_ = l_Lean_Syntax_isOfKind(v_stx_6119_, v___x_6129_);
                if v___x_6130_ == 0 {
                    crate::leanh::lean_dec_ref(v_dec_6120_);
                    crate::leanh::lean_dec(v_stx_6119_);
                    v___x_6131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                    return v___x_6131_;
                } else {
                    v___x_6132_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6133_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6132_);
                    crate::leanh::lean_inc(v___x_6133_);
                    v___x_6134_ = l_Lean_Syntax_matchesNull(v___x_6133_, v___x_6132_);
                    if v___x_6134_ == 0 {
                        crate::leanh::lean_dec(v___x_6133_);
                        crate::leanh::lean_dec_ref(v_dec_6120_);
                        crate::leanh::lean_dec(v_stx_6119_);
                        v___x_6135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                        return v___x_6135_;
                    } else {
                        v___x_6136_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6137_ = l_Lean_Syntax_getArg(v___x_6133_, v___x_6136_);
                        crate::leanh::lean_dec(v___x_6133_);
                        v___x_6138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        crate::leanh::lean_inc(v___x_6137_);
                        v___x_6139_ = l_Lean_Syntax_isOfKind(v___x_6137_, v___x_6138_);
                        if v___x_6139_ == 0 {
                            crate::leanh::lean_dec(v___x_6137_);
                            crate::leanh::lean_dec_ref(v_dec_6120_);
                            crate::leanh::lean_dec(v_stx_6119_);
                            v___x_6407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                            return v___x_6407_;
                        } else {
                            v_tk_6408_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6136_);
                            v___x_6542_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6136_);
                            v___x_6543_ = l_Lean_Syntax_isNone(v___x_6542_);
                            if v___x_6543_ == 0 {
                                v___x_6544_ = crate::leanh::lean_unsigned_to_nat(2);
                                crate::leanh::lean_inc(v___x_6542_);
                                v___x_6545_ = l_Lean_Syntax_matchesNull(v___x_6542_, v___x_6544_);
                                if v___x_6545_ == 0 {
                                    crate::leanh::lean_dec(v___x_6542_);
                                    crate::leanh::lean_dec(v_tk_6408_);
                                    crate::leanh::lean_dec(v___x_6137_);
                                    crate::leanh::lean_dec_ref(v_dec_6120_);
                                    crate::leanh::lean_dec(v_stx_6119_);
                                    v___x_6546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                                    return v___x_6546_;
                                } else {
                                    v_h_x3f_6547_ = l_Lean_Syntax_getArg(v___x_6542_, v___x_6136_);
                                    crate::leanh::lean_dec(v___x_6542_);
                                    v___x_6548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6548_, 0, v_h_x3f_6547_);
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
                                crate::leanh::lean_dec(v___x_6542_);
                                v___x_6549_ = crate::leanh::lean_box(0);
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
                v___x_6168_ = crate::leanh::lean_box((v___x_6139_) as usize);
                crate::leanh::lean_inc(v___y_6142_);
                crate::leanh::lean_inc(v___y_6154_);
                crate::leanh::lean_inc(v___y_6152_);
                crate::leanh::lean_inc_ref(v___y_6144_);
                crate::leanh::lean_inc_ref(v___y_6150_);
                v___f_6169_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__9___boxed as *mut core::ffi::c_void,
                    24,
                    15,
                );
                crate::leanh::lean_closure_set(v___f_6169_, 0, v___x_6167_);
                crate::leanh::lean_closure_set(v___f_6169_, 1, v___x_6136_);
                crate::leanh::lean_closure_set(v___f_6169_, 2, v___y_6156_);
                crate::leanh::lean_closure_set(v___f_6169_, 3, v___y_6150_);
                crate::leanh::lean_closure_set(v___f_6169_, 4, v___y_6144_);
                crate::leanh::lean_closure_set(v___f_6169_, 5, v___y_6152_);
                crate::leanh::lean_closure_set(v___f_6169_, 6, v___y_6146_);
                crate::leanh::lean_closure_set(v___f_6169_, 7, v___y_6153_);
                crate::leanh::lean_closure_set(v___f_6169_, 8, v___y_6147_);
                crate::leanh::lean_closure_set(v___f_6169_, 9, v___y_6148_);
                crate::leanh::lean_closure_set(v___f_6169_, 10, v___x_6168_);
                crate::leanh::lean_closure_set(v___f_6169_, 11, v___y_6154_);
                crate::leanh::lean_closure_set(v___f_6169_, 12, v___y_6142_);
                crate::leanh::lean_closure_set(v___f_6169_, 13, v___y_6141_);
                crate::leanh::lean_closure_set(v___f_6169_, 14, v___x_6132_);
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
                if crate::leanh::lean_obj_tag(v___x_6171_) == 0 {
                    v_a_6172_ = crate::leanh::lean_ctor_get(v___x_6171_, 0);
                    crate::leanh::lean_inc(v_a_6172_);
                    crate::leanh::lean_dec_ref_known(v___x_6171_, 1);
                    v_doBlockResultType_6173_ = crate::leanh::lean_ctor_get(v___y_6159_, 3);
                    v___x_6174_ = crate::leanh::lean_box((v___y_6145_) as usize);
                    crate::leanh::lean_inc(v___y_6155_);
                    crate::leanh::lean_inc_ref(v_doBlockResultType_6173_);
                    v___y_6175_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__10___boxed as *mut core::ffi::c_void,
                        19,
                        11,
                    );
                    crate::leanh::lean_closure_set(v___y_6175_, 0, v___x_6174_);
                    crate::leanh::lean_closure_set(v___y_6175_, 1, v___y_6144_);
                    crate::leanh::lean_closure_set(v___y_6175_, 2, v___y_6149_);
                    crate::leanh::lean_closure_set(v___y_6175_, 3, v_doBlockResultType_6173_);
                    crate::leanh::lean_closure_set(v___y_6175_, 4, v___y_6150_);
                    crate::leanh::lean_closure_set(v___y_6175_, 5, v___y_6155_);
                    crate::leanh::lean_closure_set(v___y_6175_, 6, v___y_6152_);
                    crate::leanh::lean_closure_set(v___y_6175_, 7, v___y_6143_);
                    crate::leanh::lean_closure_set(v___y_6175_, 8, v___y_6151_);
                    crate::leanh::lean_closure_set(v___y_6175_, 9, v___x_6136_);
                    crate::leanh::lean_closure_set(v___y_6175_, 10, v___x_6132_);
                    v___x_6176_ = crate::leanh::lean_box((v___x_6139_) as usize);
                    v___f_6177_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__11___boxed as *mut core::ffi::c_void,
                        13,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_6177_, 0, v___y_6154_);
                    crate::leanh::lean_closure_set(v___f_6177_, 1, v___y_6175_);
                    crate::leanh::lean_closure_set(v___f_6177_, 2, v___x_6132_);
                    crate::leanh::lean_closure_set(v___f_6177_, 3, v___x_6176_);
                    crate::leanh::lean_inc_ref(v___y_6165_);
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
                    if crate::leanh::lean_obj_tag(v___x_6178_) == 0 {
                        v_a_6179_ = crate::leanh::lean_ctor_get(v___x_6178_, 0);
                        crate::leanh::lean_inc(v_a_6179_);
                        crate::leanh::lean_dec_ref_known(v___x_6178_, 1);
                        v___x_6180_ = l_Lean_Expr_app___override(v___y_6164_, v_a_6172_);
                        crate::leanh::lean_inc_ref(v_doBlockResultType_6173_);
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
                        crate::leanh::lean_dec(v_a_6172_);
                        crate::leanh::lean_dec_ref(v___y_6165_);
                        crate::leanh::lean_dec_ref(v___y_6164_);
                        return v___x_6178_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6165_);
                    crate::leanh::lean_dec_ref(v___y_6164_);
                    crate::leanh::lean_dec(v___y_6154_);
                    crate::leanh::lean_dec(v___y_6152_);
                    crate::leanh::lean_dec_ref(v___y_6151_);
                    crate::leanh::lean_dec_ref(v___y_6150_);
                    crate::leanh::lean_dec(v___y_6149_);
                    crate::leanh::lean_dec_ref(v___y_6144_);
                    crate::leanh::lean_dec_ref(v___y_6143_);
                    crate::leanh::lean_dec(v___y_6142_);
                    return v___x_6171_;
                }
            }
            2 => {
                v___x_6216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17;
                v___x_6217_ = l_Lean_Core_mkFreshUserName(v___x_6216_, v___y_6214_, v___y_6215_);
                if crate::leanh::lean_obj_tag(v___x_6217_) == 0 {
                    if crate::leanh::lean_obj_tag(v___y_6204_) == 1 {
                        if crate::leanh::lean_obj_tag(v_snd_6208_) == 1 {
                            crate::leanh::lean_dec_ref(v___y_6203_);
                            v_a_6218_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
                            crate::leanh::lean_inc(v_a_6218_);
                            crate::leanh::lean_dec_ref_known(v___x_6217_, 1);
                            v_val_6219_ = crate::leanh::lean_ctor_get(v___y_6204_, 0);
                            crate::leanh::lean_inc(v_val_6219_);
                            crate::leanh::lean_dec_ref_known(v___y_6204_, 1);
                            v_val_6220_ = crate::leanh::lean_ctor_get(v_snd_6208_, 0);
                            crate::leanh::lean_inc(v_val_6220_);
                            crate::leanh::lean_dec_ref_known(v_snd_6208_, 1);
                            v___f_6221_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_elabDoFor___lam__12___boxed
                                    as *mut core::ffi::c_void,
                                16,
                                7,
                            );
                            crate::leanh::lean_closure_set(v___f_6221_, 0, v___y_6197_);
                            crate::leanh::lean_closure_set(v___f_6221_, 1, v___y_6192_);
                            crate::leanh::lean_closure_set(v___f_6221_, 2, v___x_6136_);
                            crate::leanh::lean_closure_set(v___f_6221_, 3, v___y_6183_);
                            crate::leanh::lean_closure_set(v___f_6221_, 4, v___y_6200_);
                            crate::leanh::lean_closure_set(v___f_6221_, 5, v_val_6220_);
                            crate::leanh::lean_closure_set(v___f_6221_, 6, v___y_6187_);
                            v___x_6222_ = l_Lean_TSyntax_getId(v___y_6206_);
                            crate::leanh::lean_dec(v___y_6206_);
                            v___x_6223_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6223_, 0, v___x_6222_);
                            crate::leanh::lean_ctor_set(v___x_6223_, 1, v___y_6205_);
                            v___x_6224_ = l_Lean_TSyntax_getId(v_val_6219_);
                            crate::leanh::lean_dec(v_val_6219_);
                            v___x_6225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6225_, 0, v___x_6224_);
                            crate::leanh::lean_ctor_set(v___x_6225_, 1, v___f_6221_);
                            v___x_6226_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_6227_ = lean_mk_empty_array_with_capacity(v___x_6226_);
                            v___x_6228_ = lean_array_push(v___x_6227_, v___x_6223_);
                            v___x_6229_ = lean_array_push(v___x_6228_, v___x_6225_);
                            crate::leanh::lean_inc_ref(v___y_6189_);
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
                            crate::leanh::lean_dec(v___y_6206_);
                            crate::leanh::lean_dec_ref(v___y_6205_);
                            crate::leanh::lean_dec_ref(v___y_6200_);
                            crate::leanh::lean_dec(v___y_6197_);
                            crate::leanh::lean_dec(v___y_6192_);
                            crate::leanh::lean_dec_ref(v___y_6187_);
                            crate::leanh::lean_dec_ref(v___y_6183_);
                            v_a_6230_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
                            crate::leanh::lean_inc(v_a_6230_);
                            crate::leanh::lean_dec_ref_known(v___x_6217_, 1);
                            v___x_6231_ =
                                crate::leanh::lean_apply_2(v___y_6203_, v___y_6204_, v_snd_6208_);
                            crate::leanh::lean_inc_ref(v___y_6189_);
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
                        crate::leanh::lean_dec(v___y_6206_);
                        crate::leanh::lean_dec_ref(v___y_6205_);
                        crate::leanh::lean_dec_ref(v___y_6200_);
                        crate::leanh::lean_dec(v___y_6197_);
                        crate::leanh::lean_dec(v___y_6192_);
                        crate::leanh::lean_dec_ref(v___y_6187_);
                        crate::leanh::lean_dec_ref(v___y_6183_);
                        v_a_6232_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
                        crate::leanh::lean_inc(v_a_6232_);
                        crate::leanh::lean_dec_ref_known(v___x_6217_, 1);
                        v___x_6233_ =
                            crate::leanh::lean_apply_2(v___y_6203_, v___y_6204_, v_snd_6208_);
                        crate::leanh::lean_inc_ref(v___y_6189_);
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
                    crate::leanh::lean_dec(v_snd_6208_);
                    crate::leanh::lean_dec_ref(v_fst_6207_);
                    crate::leanh::lean_dec(v___y_6206_);
                    crate::leanh::lean_dec_ref(v___y_6205_);
                    crate::leanh::lean_dec(v___y_6204_);
                    crate::leanh::lean_dec_ref(v___y_6203_);
                    crate::leanh::lean_dec(v___y_6202_);
                    crate::leanh::lean_dec_ref(v___y_6200_);
                    crate::leanh::lean_dec(v___y_6199_);
                    crate::leanh::lean_dec_ref(v___y_6198_);
                    crate::leanh::lean_dec(v___y_6197_);
                    crate::leanh::lean_dec(v___y_6196_);
                    crate::leanh::lean_dec_ref(v___y_6195_);
                    crate::leanh::lean_dec_ref(v___y_6194_);
                    crate::leanh::lean_dec(v___y_6193_);
                    crate::leanh::lean_dec(v___y_6192_);
                    crate::leanh::lean_dec(v___y_6191_);
                    crate::leanh::lean_dec(v___y_6190_);
                    crate::leanh::lean_dec_ref(v___y_6189_);
                    crate::leanh::lean_dec_ref(v___y_6187_);
                    crate::leanh::lean_dec_ref(v___y_6186_);
                    crate::leanh::lean_dec_ref(v___y_6185_);
                    crate::leanh::lean_dec(v___y_6184_);
                    crate::leanh::lean_dec_ref(v___y_6183_);
                    v_a_6234_ = crate::leanh::lean_ctor_get(v___x_6217_, 0);
                    v_isSharedCheck_6241_ = (!crate::leanh::lean_is_exclusive(v___x_6217_)) as u8;
                    if v_isSharedCheck_6241_ == 0 {
                        v___x_6236_ = v___x_6217_;
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6234_);
                        crate::leanh::lean_dec(v___x_6217_);
                        v___x_6236_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6239_;
            }
            5 => {
                v___x_6277_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v___y_6255_);
                crate::leanh::lean_inc(v___y_6259_);
                crate::leanh::lean_inc_ref(v___y_6263_);
                crate::leanh::lean_inc(v___y_6261_);
                crate::leanh::lean_inc_ref(v___y_6273_);
                crate::leanh::lean_inc(v___y_6266_);
                crate::leanh::lean_inc_ref(v___y_6260_);
                v___x_6278_ = crate::leanh::lean_apply_8(
                    v___y_6255_,
                    v___x_6277_,
                    v___y_6260_,
                    v___y_6266_,
                    v___y_6273_,
                    v___y_6261_,
                    v___y_6263_,
                    v___y_6259_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6278_) == 0 {
                    v_a_6279_ = crate::leanh::lean_ctor_get(v___x_6278_, 0);
                    crate::leanh::lean_inc(v_a_6279_);
                    crate::leanh::lean_dec_ref_known(v___x_6278_, 1);
                    v_m_6280_ = crate::leanh::lean_ctor_get(v___y_6274_, 0);
                    v_u_6281_ = crate::leanh::lean_ctor_get(v___y_6274_, 1);
                    v_v_6282_ = crate::leanh::lean_ctor_get(v___y_6274_, 2);
                    crate::leanh::lean_inc(v_u_6281_);
                    v___x_6283_ = l_Lean_Meta_mkProdMkN(
                        v_a_6279_,
                        v_u_6281_,
                        v___y_6273_,
                        v___y_6261_,
                        v___y_6263_,
                        v___y_6259_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6283_) == 0 {
                        v_a_6284_ = crate::leanh::lean_ctor_get(v___x_6283_, 0);
                        crate::leanh::lean_inc(v_a_6284_);
                        crate::leanh::lean_dec_ref_known(v___x_6283_, 1);
                        if crate::leanh::lean_obj_tag(v___y_6262_) == 0 {
                            v_fst_6285_ = crate::leanh::lean_ctor_get(v_a_6284_, 0);
                            v_snd_6286_ = crate::leanh::lean_ctor_get(v_a_6284_, 1);
                            v_isSharedCheck_6305_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6284_)) as u8;
                            if v_isSharedCheck_6305_ == 0 {
                                v___x_6288_ = v_a_6284_;
                                v_isShared_6289_ = v_isSharedCheck_6305_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_6286_);
                                crate::leanh::lean_inc(v_fst_6285_);
                                crate::leanh::lean_dec(v_a_6284_);
                                v___x_6288_ = crate::leanh::lean_box(0);
                                v_isShared_6289_ = v_isSharedCheck_6305_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_fst_6306_ = crate::leanh::lean_ctor_get(v_a_6284_, 0);
                            v_snd_6307_ = crate::leanh::lean_ctor_get(v_a_6284_, 1);
                            v_isSharedCheck_6342_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6284_)) as u8;
                            if v_isSharedCheck_6342_ == 0 {
                                v___x_6309_ = v_a_6284_;
                                v_isShared_6310_ = v_isSharedCheck_6342_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_6307_);
                                crate::leanh::lean_inc(v_fst_6306_);
                                crate::leanh::lean_dec(v_a_6284_);
                                v___x_6309_ = crate::leanh::lean_box(0);
                                v_isShared_6310_ = v_isSharedCheck_6342_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_6276_);
                        crate::leanh::lean_dec(v___y_6275_);
                        crate::leanh::lean_dec_ref(v___y_6272_);
                        crate::leanh::lean_dec_ref(v___y_6269_);
                        crate::leanh::lean_dec(v___y_6268_);
                        crate::leanh::lean_dec(v___y_6267_);
                        crate::leanh::lean_dec_ref(v___y_6265_);
                        crate::leanh::lean_dec_ref(v___y_6264_);
                        crate::leanh::lean_dec(v___y_6262_);
                        crate::leanh::lean_dec_ref(v___y_6258_);
                        crate::leanh::lean_dec(v___y_6257_);
                        crate::leanh::lean_dec_ref(v___y_6256_);
                        crate::leanh::lean_dec_ref(v___y_6255_);
                        crate::leanh::lean_dec(v___y_6254_);
                        crate::leanh::lean_dec_ref(v___y_6253_);
                        crate::leanh::lean_dec_ref(v___y_6252_);
                        crate::leanh::lean_dec(v___y_6251_);
                        crate::leanh::lean_dec(v___y_6250_);
                        crate::leanh::lean_dec(v___y_6249_);
                        crate::leanh::lean_dec_ref(v___y_6247_);
                        crate::leanh::lean_dec_ref(v___y_6246_);
                        crate::leanh::lean_dec_ref(v___y_6245_);
                        crate::leanh::lean_dec(v___y_6244_);
                        crate::leanh::lean_dec_ref(v___y_6243_);
                        v_a_6343_ = crate::leanh::lean_ctor_get(v___x_6283_, 0);
                        v_isSharedCheck_6350_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6283_)) as u8;
                        if v_isSharedCheck_6350_ == 0 {
                            v___x_6345_ = v___x_6283_;
                            v_isShared_6346_ = v_isSharedCheck_6350_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6343_);
                            crate::leanh::lean_dec(v___x_6283_);
                            v___x_6345_ = crate::leanh::lean_box(0);
                            v_isShared_6346_ = v_isSharedCheck_6350_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6276_);
                    crate::leanh::lean_dec(v___y_6275_);
                    crate::leanh::lean_dec_ref(v___y_6272_);
                    crate::leanh::lean_dec_ref(v___y_6269_);
                    crate::leanh::lean_dec(v___y_6268_);
                    crate::leanh::lean_dec(v___y_6267_);
                    crate::leanh::lean_dec_ref(v___y_6265_);
                    crate::leanh::lean_dec_ref(v___y_6264_);
                    crate::leanh::lean_dec(v___y_6262_);
                    crate::leanh::lean_dec_ref(v___y_6258_);
                    crate::leanh::lean_dec(v___y_6257_);
                    crate::leanh::lean_dec_ref(v___y_6256_);
                    crate::leanh::lean_dec_ref(v___y_6255_);
                    crate::leanh::lean_dec(v___y_6254_);
                    crate::leanh::lean_dec_ref(v___y_6253_);
                    crate::leanh::lean_dec_ref(v___y_6252_);
                    crate::leanh::lean_dec(v___y_6251_);
                    crate::leanh::lean_dec(v___y_6250_);
                    crate::leanh::lean_dec(v___y_6249_);
                    crate::leanh::lean_dec_ref(v___y_6247_);
                    crate::leanh::lean_dec_ref(v___y_6246_);
                    crate::leanh::lean_dec_ref(v___y_6245_);
                    crate::leanh::lean_dec(v___y_6244_);
                    crate::leanh::lean_dec_ref(v___y_6243_);
                    v_a_6351_ = crate::leanh::lean_ctor_get(v___x_6278_, 0);
                    v_isSharedCheck_6358_ = (!crate::leanh::lean_is_exclusive(v___x_6278_)) as u8;
                    if v_isSharedCheck_6358_ == 0 {
                        v___x_6353_ = v___x_6278_;
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6351_);
                        crate::leanh::lean_dec(v___x_6278_);
                        v___x_6353_ = crate::leanh::lean_box(0);
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6290_ = l_Lean_Elab_Do_elabDoFor___closed__1;
                v___x_6291_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_v_6282_);
                if v_isShared_6289_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6288_, 1);
                    crate::leanh::lean_ctor_set(v___x_6288_, 1, v___x_6291_);
                    crate::leanh::lean_ctor_set(v___x_6288_, 0, v_v_6282_);
                    v___x_6293_ = v___x_6288_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6304_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_v_6282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6304_, 1, v___x_6291_);
                    v___x_6293_ = v_reuseFailAlloc_6304_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc(v_u_6281_);
                v___x_6294_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6294_, 0, v_u_6281_);
                crate::leanh::lean_ctor_set(v___x_6294_, 1, v___x_6293_);
                v___x_6295_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6295_, 0, v___y_6267_);
                crate::leanh::lean_ctor_set(v___x_6295_, 1, v___x_6294_);
                v___x_6296_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6296_, 0, v___y_6268_);
                crate::leanh::lean_ctor_set(v___x_6296_, 1, v___x_6295_);
                crate::leanh::lean_inc_ref(v___x_6296_);
                v___x_6297_ = l_Lean_mkConst(v___x_6290_, v___x_6296_);
                crate::leanh::lean_inc_ref(v___y_6258_);
                crate::leanh::lean_inc_ref(v___y_6272_);
                crate::leanh::lean_inc_ref(v_m_6280_);
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
                if crate::leanh::lean_obj_tag(v___x_6299_) == 0 {
                    v_a_6300_ = crate::leanh::lean_ctor_get(v___x_6299_, 0);
                    crate::leanh::lean_inc(v_a_6300_);
                    crate::leanh::lean_dec_ref_known(v___x_6299_, 1);
                    v___x_6301_ = l_Lean_Elab_Do_elabDoFor___closed__3;
                    v___x_6302_ = l_Lean_mkConst(v___x_6301_, v___x_6296_);
                    crate::leanh::lean_inc(v_snd_6286_);
                    crate::leanh::lean_inc_ref(v_m_6280_);
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
                    crate::leanh::lean_inc(v_u_6281_);
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
                    crate::leanh::lean_dec_ref_known(v___x_6296_, 2);
                    crate::leanh::lean_dec(v_snd_6286_);
                    crate::leanh::lean_dec(v_fst_6285_);
                    crate::leanh::lean_dec(v___y_6276_);
                    crate::leanh::lean_dec(v___y_6275_);
                    crate::leanh::lean_dec_ref(v___y_6272_);
                    crate::leanh::lean_dec_ref(v___y_6269_);
                    crate::leanh::lean_dec_ref(v___y_6265_);
                    crate::leanh::lean_dec_ref(v___y_6264_);
                    crate::leanh::lean_dec_ref(v___y_6258_);
                    crate::leanh::lean_dec(v___y_6257_);
                    crate::leanh::lean_dec_ref(v___y_6256_);
                    crate::leanh::lean_dec_ref(v___y_6255_);
                    crate::leanh::lean_dec(v___y_6254_);
                    crate::leanh::lean_dec_ref(v___y_6253_);
                    crate::leanh::lean_dec_ref(v___y_6252_);
                    crate::leanh::lean_dec(v___y_6251_);
                    crate::leanh::lean_dec(v___y_6250_);
                    crate::leanh::lean_dec(v___y_6249_);
                    crate::leanh::lean_dec_ref(v___y_6247_);
                    crate::leanh::lean_dec_ref(v___y_6246_);
                    crate::leanh::lean_dec_ref(v___y_6245_);
                    crate::leanh::lean_dec(v___y_6244_);
                    crate::leanh::lean_dec_ref(v___y_6243_);
                    return v___x_6299_;
                }
            }
            8 => {
                v___x_6311_ = l_Lean_Elab_Do_elabDoFor___closed__4;
                v___x_6312_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_6268_);
                if v_isShared_6310_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6309_, 1);
                    crate::leanh::lean_ctor_set(v___x_6309_, 1, v___x_6312_);
                    crate::leanh::lean_ctor_set(v___x_6309_, 0, v___y_6268_);
                    v___x_6314_ = v___x_6309_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6341_, 0, v___y_6268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6341_, 1, v___x_6312_);
                    v___x_6314_ = v_reuseFailAlloc_6341_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc(v___y_6267_);
                v___x_6315_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6315_, 0, v___y_6267_);
                crate::leanh::lean_ctor_set(v___x_6315_, 1, v___x_6314_);
                v___x_6316_ = l_Lean_mkConst(v___x_6311_, v___x_6315_);
                crate::leanh::lean_inc_ref(v___y_6272_);
                crate::leanh::lean_inc_ref(v___y_6258_);
                v___x_6317_ = l_Lean_mkAppB(v___x_6316_, v___y_6258_, v___y_6272_);
                v___x_6318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6318_, 0, v___x_6317_);
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
                if crate::leanh::lean_obj_tag(v___x_6320_) == 0 {
                    v_a_6321_ = crate::leanh::lean_ctor_get(v___x_6320_, 0);
                    crate::leanh::lean_inc_n(v_a_6321_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6320_, 1);
                    v___x_6322_ = l_Lean_Elab_Do_elabDoFor___closed__8;
                    crate::leanh::lean_inc(v_v_6282_);
                    v___x_6323_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6323_, 0, v_v_6282_);
                    crate::leanh::lean_ctor_set(v___x_6323_, 1, v___x_6312_);
                    crate::leanh::lean_inc(v_u_6281_);
                    v___x_6324_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6324_, 0, v_u_6281_);
                    crate::leanh::lean_ctor_set(v___x_6324_, 1, v___x_6323_);
                    v___x_6325_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6325_, 0, v___y_6267_);
                    crate::leanh::lean_ctor_set(v___x_6325_, 1, v___x_6324_);
                    v___x_6326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6326_, 0, v___y_6268_);
                    crate::leanh::lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                    crate::leanh::lean_inc_ref(v___x_6326_);
                    v___x_6327_ = l_Lean_mkConst(v___x_6322_, v___x_6326_);
                    crate::leanh::lean_inc_ref(v___y_6258_);
                    crate::leanh::lean_inc_ref(v___y_6272_);
                    crate::leanh::lean_inc_ref(v_m_6280_);
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
                    if crate::leanh::lean_obj_tag(v___x_6329_) == 0 {
                        v_a_6330_ = crate::leanh::lean_ctor_get(v___x_6329_, 0);
                        v_isSharedCheck_6340_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6329_)) as u8;
                        if v_isSharedCheck_6340_ == 0 {
                            v___x_6332_ = v___x_6329_;
                            v_isShared_6333_ = v_isSharedCheck_6340_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6330_);
                            crate::leanh::lean_dec(v___x_6329_);
                            v___x_6332_ = crate::leanh::lean_box(0);
                            v_isShared_6333_ = v_isSharedCheck_6340_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_6326_, 2);
                        crate::leanh::lean_dec(v_a_6321_);
                        crate::leanh::lean_dec(v_snd_6307_);
                        crate::leanh::lean_dec_ref_known(v___y_6262_, 1);
                        crate::leanh::lean_dec(v_fst_6306_);
                        crate::leanh::lean_dec(v___y_6276_);
                        crate::leanh::lean_dec(v___y_6275_);
                        crate::leanh::lean_dec_ref(v___y_6272_);
                        crate::leanh::lean_dec_ref(v___y_6269_);
                        crate::leanh::lean_dec_ref(v___y_6265_);
                        crate::leanh::lean_dec_ref(v___y_6264_);
                        crate::leanh::lean_dec_ref(v___y_6258_);
                        crate::leanh::lean_dec(v___y_6257_);
                        crate::leanh::lean_dec_ref(v___y_6256_);
                        crate::leanh::lean_dec_ref(v___y_6255_);
                        crate::leanh::lean_dec(v___y_6254_);
                        crate::leanh::lean_dec_ref(v___y_6253_);
                        crate::leanh::lean_dec_ref(v___y_6252_);
                        crate::leanh::lean_dec(v___y_6251_);
                        crate::leanh::lean_dec(v___y_6250_);
                        crate::leanh::lean_dec(v___y_6249_);
                        crate::leanh::lean_dec_ref(v___y_6247_);
                        crate::leanh::lean_dec_ref(v___y_6246_);
                        crate::leanh::lean_dec_ref(v___y_6245_);
                        crate::leanh::lean_dec(v___y_6244_);
                        crate::leanh::lean_dec_ref(v___y_6243_);
                        return v___x_6329_;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_6307_);
                    crate::leanh::lean_dec_ref_known(v___y_6262_, 1);
                    crate::leanh::lean_dec(v_fst_6306_);
                    crate::leanh::lean_dec(v___y_6276_);
                    crate::leanh::lean_dec(v___y_6275_);
                    crate::leanh::lean_dec_ref(v___y_6272_);
                    crate::leanh::lean_dec_ref(v___y_6269_);
                    crate::leanh::lean_dec(v___y_6268_);
                    crate::leanh::lean_dec(v___y_6267_);
                    crate::leanh::lean_dec_ref(v___y_6265_);
                    crate::leanh::lean_dec_ref(v___y_6264_);
                    crate::leanh::lean_dec_ref(v___y_6258_);
                    crate::leanh::lean_dec(v___y_6257_);
                    crate::leanh::lean_dec_ref(v___y_6256_);
                    crate::leanh::lean_dec_ref(v___y_6255_);
                    crate::leanh::lean_dec(v___y_6254_);
                    crate::leanh::lean_dec_ref(v___y_6253_);
                    crate::leanh::lean_dec_ref(v___y_6252_);
                    crate::leanh::lean_dec(v___y_6251_);
                    crate::leanh::lean_dec(v___y_6250_);
                    crate::leanh::lean_dec(v___y_6249_);
                    crate::leanh::lean_dec_ref(v___y_6247_);
                    crate::leanh::lean_dec_ref(v___y_6246_);
                    crate::leanh::lean_dec_ref(v___y_6245_);
                    crate::leanh::lean_dec(v___y_6244_);
                    crate::leanh::lean_dec_ref(v___y_6243_);
                    return v___x_6320_;
                }
            }
            10 => {
                v___x_6334_ = l_Lean_Elab_Do_elabDoFor___closed__10;
                v___x_6335_ = l_Lean_mkConst(v___x_6334_, v___x_6326_);
                crate::leanh::lean_inc(v_snd_6307_);
                crate::leanh::lean_inc(v_a_6321_);
                crate::leanh::lean_inc_ref(v_m_6280_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_6332_, 1);
                    crate::leanh::lean_ctor_set(v___x_6332_, 0, v_a_6321_);
                    v___x_6338_ = v___x_6332_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6321_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc(v_u_6281_);
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
                    v_reuseFailAlloc_6349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6349_, 0, v_a_6343_);
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
                    v_reuseFailAlloc_6357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
                    v___x_6356_ = v_reuseFailAlloc_6357_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6356_;
            }
            16 => {
                v_returnsEarly_6394_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6378_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2) as u32,
                );
                crate::leanh::lean_dec_ref(v___y_6378_);
                v___x_6395_ = crate::leanh::lean_box((v_returnsEarly_6394_) as usize);
                v___x_6396_ = crate::leanh::lean_box((v___y_6371_) as usize);
                crate::leanh::lean_inc_ref(v___y_6369_);
                crate::leanh::lean_inc_ref(v___y_6375_);
                crate::leanh::lean_inc_ref(v___y_6393_);
                v___f_6397_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_6397_, 0, v___y_6393_);
                crate::leanh::lean_closure_set(v___f_6397_, 1, v___y_6375_);
                crate::leanh::lean_closure_set(v___f_6397_, 2, v___x_6395_);
                crate::leanh::lean_closure_set(v___f_6397_, 3, v___x_6136_);
                crate::leanh::lean_closure_set(v___f_6397_, 4, v___y_6369_);
                crate::leanh::lean_closure_set(v___f_6397_, 5, v___x_6396_);
                if v_returnsEarly_6394_ == 0 {
                    crate::leanh::lean_dec(v___y_6385_);
                    v_sz_6398_ = lean_array_size(v___y_6393_);
                    v___x_6399_ = 0usize;
                    crate::leanh::lean_inc_ref(v___y_6393_);
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
                    crate::leanh::lean_inc_ref(v___y_6393_);
                    v___x_6404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_6402_, v___x_6403_, v___y_6393_);
                    v___x_6405_ = lean_array_to_list(v___x_6404_);
                    v___x_6406_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6406_, 0, v___y_6385_);
                    crate::leanh::lean_ctor_set(v___x_6406_, 1, v___x_6405_);
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
                crate::leanh::lean_inc(v_x_6418_);
                v___x_6420_ = l_Lean_Syntax_isOfKind(v_x_6418_, v___x_6419_);
                if v___x_6420_ == 0 {
                    crate::leanh::lean_dec(v_x_6418_);
                    crate::leanh::lean_dec(v_h_x3f_6410_);
                    crate::leanh::lean_dec(v_tk_6408_);
                    crate::leanh::lean_dec(v___x_6137_);
                    crate::leanh::lean_dec_ref(v_dec_6120_);
                    crate::leanh::lean_dec(v_stx_6119_);
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
                    crate::leanh::lean_dec(v_tk_6408_);
                    if crate::leanh::lean_obj_tag(v___x_6422_) == 0 {
                        v_a_6423_ = crate::leanh::lean_ctor_get(v___x_6422_, 0);
                        crate::leanh::lean_inc(v_a_6423_);
                        crate::leanh::lean_dec_ref_known(v___x_6422_, 1);
                        v___x_6424_ = lean_mk_empty_array_with_capacity(v___x_6132_);
                        crate::leanh::lean_inc(v_x_6418_);
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
                        crate::leanh::lean_dec_ref(v___x_6425_);
                        if crate::leanh::lean_obj_tag(v___x_6426_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6426_, 1);
                            v___x_6427_ = l_Lean_Meta_mkFreshLevelMVar(
                                v___y_6414_,
                                v___y_6415_,
                                v___y_6416_,
                                v___y_6417_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6427_) == 0 {
                                v_a_6428_ = crate::leanh::lean_ctor_get(v___x_6427_, 0);
                                crate::leanh::lean_inc(v_a_6428_);
                                crate::leanh::lean_dec_ref_known(v___x_6427_, 1);
                                v___x_6429_ = l_Lean_Meta_mkFreshLevelMVar(
                                    v___y_6414_,
                                    v___y_6415_,
                                    v___y_6416_,
                                    v___y_6417_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6429_) == 0 {
                                    v_a_6430_ = crate::leanh::lean_ctor_get(v___x_6429_, 0);
                                    crate::leanh::lean_inc(v_a_6430_);
                                    crate::leanh::lean_dec_ref_known(v___x_6429_, 1);
                                    crate::leanh::lean_inc(v_a_6428_);
                                    v___x_6431_ = l_Lean_Level_succ___override(v_a_6428_);
                                    v___x_6432_ = l_Lean_mkSort(v___x_6431_);
                                    v___x_6433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6433_, 0, v___x_6432_);
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
                                    if crate::leanh::lean_obj_tag(v___x_6436_) == 0 {
                                        v_a_6437_ = crate::leanh::lean_ctor_get(v___x_6436_, 0);
                                        v_isSharedCheck_6509_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6436_)) as u8;
                                        if v_isSharedCheck_6509_ == 0 {
                                            v___x_6439_ = v___x_6436_;
                                            v_isShared_6440_ = v_isSharedCheck_6509_;
                                            state = 18;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6437_);
                                            crate::leanh::lean_dec(v___x_6436_);
                                            v___x_6439_ = crate::leanh::lean_box(0);
                                            v_isShared_6440_ = v_isSharedCheck_6509_;
                                            state = 18;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6430_);
                                        crate::leanh::lean_dec(v_a_6428_);
                                        crate::leanh::lean_dec(v_a_6423_);
                                        crate::leanh::lean_dec(v_x_6418_);
                                        crate::leanh::lean_dec(v_h_x3f_6410_);
                                        crate::leanh::lean_dec(v___x_6137_);
                                        crate::leanh::lean_dec(v_stx_6119_);
                                        return v___x_6436_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6428_);
                                    crate::leanh::lean_dec(v_a_6423_);
                                    crate::leanh::lean_dec(v_x_6418_);
                                    crate::leanh::lean_dec(v_h_x3f_6410_);
                                    crate::leanh::lean_dec(v___x_6137_);
                                    crate::leanh::lean_dec(v_stx_6119_);
                                    v_a_6510_ = crate::leanh::lean_ctor_get(v___x_6429_, 0);
                                    v_isSharedCheck_6517_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6429_)) as u8;
                                    if v_isSharedCheck_6517_ == 0 {
                                        v___x_6512_ = v___x_6429_;
                                        v_isShared_6513_ = v_isSharedCheck_6517_;
                                        state = 28;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6510_);
                                        crate::leanh::lean_dec(v___x_6429_);
                                        v___x_6512_ = crate::leanh::lean_box(0);
                                        v_isShared_6513_ = v_isSharedCheck_6517_;
                                        state = 28;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6423_);
                                crate::leanh::lean_dec(v_x_6418_);
                                crate::leanh::lean_dec(v_h_x3f_6410_);
                                crate::leanh::lean_dec(v___x_6137_);
                                crate::leanh::lean_dec(v_stx_6119_);
                                v_a_6518_ = crate::leanh::lean_ctor_get(v___x_6427_, 0);
                                v_isSharedCheck_6525_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6427_)) as u8;
                                if v_isSharedCheck_6525_ == 0 {
                                    v___x_6520_ = v___x_6427_;
                                    v_isShared_6521_ = v_isSharedCheck_6525_;
                                    state = 30;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6518_);
                                    crate::leanh::lean_dec(v___x_6427_);
                                    v___x_6520_ = crate::leanh::lean_box(0);
                                    v_isShared_6521_ = v_isSharedCheck_6525_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6423_);
                            crate::leanh::lean_dec(v_x_6418_);
                            crate::leanh::lean_dec(v_h_x3f_6410_);
                            crate::leanh::lean_dec(v___x_6137_);
                            crate::leanh::lean_dec(v_stx_6119_);
                            v_a_6526_ = crate::leanh::lean_ctor_get(v___x_6426_, 0);
                            v_isSharedCheck_6533_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6426_)) as u8;
                            if v_isSharedCheck_6533_ == 0 {
                                v___x_6528_ = v___x_6426_;
                                v_isShared_6529_ = v_isSharedCheck_6533_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6526_);
                                crate::leanh::lean_dec(v___x_6426_);
                                v___x_6528_ = crate::leanh::lean_box(0);
                                v_isShared_6529_ = v_isSharedCheck_6533_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_6418_);
                        crate::leanh::lean_dec(v_h_x3f_6410_);
                        crate::leanh::lean_dec(v___x_6137_);
                        crate::leanh::lean_dec(v_stx_6119_);
                        v_a_6534_ = crate::leanh::lean_ctor_get(v___x_6422_, 0);
                        v_isSharedCheck_6541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6422_)) as u8;
                        if v_isSharedCheck_6541_ == 0 {
                            v___x_6536_ = v___x_6422_;
                            v_isShared_6537_ = v_isSharedCheck_6541_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6534_);
                            crate::leanh::lean_dec(v___x_6422_);
                            v___x_6536_ = crate::leanh::lean_box(0);
                            v_isShared_6537_ = v_isSharedCheck_6541_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            18 => {
                crate::leanh::lean_inc(v_a_6430_);
                v___x_6441_ = l_Lean_Level_succ___override(v_a_6430_);
                v___x_6442_ = l_Lean_mkSort(v___x_6441_);
                if v_isShared_6440_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6439_, 1);
                    crate::leanh::lean_ctor_set(v___x_6439_, 0, v___x_6442_);
                    v___x_6444_ = v___x_6439_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 0, v___x_6442_);
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
                if crate::leanh::lean_obj_tag(v___x_6446_) == 0 {
                    v_a_6447_ = crate::leanh::lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6507_ = (!crate::leanh::lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6449_ = v___x_6446_;
                        v_isShared_6450_ = v_isSharedCheck_6507_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6447_);
                        crate::leanh::lean_dec(v___x_6446_);
                        v___x_6449_ = crate::leanh::lean_box(0);
                        v_isShared_6450_ = v_isSharedCheck_6507_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6437_);
                    crate::leanh::lean_dec(v_a_6430_);
                    crate::leanh::lean_dec(v_a_6428_);
                    crate::leanh::lean_dec(v_a_6423_);
                    crate::leanh::lean_dec(v_x_6418_);
                    crate::leanh::lean_dec(v_h_x3f_6410_);
                    crate::leanh::lean_dec(v___x_6137_);
                    crate::leanh::lean_dec(v_stx_6119_);
                    return v___x_6446_;
                }
            }
            20 => {
                v___x_6451_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6452_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6451_);
                crate::leanh::lean_dec(v___x_6137_);
                crate::leanh::lean_inc(v_a_6447_);
                if v_isShared_6450_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6449_, 1);
                    v___x_6454_ = v___x_6449_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6447_);
                    v___x_6454_ = v_reuseFailAlloc_6506_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_6455_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_6456_) == 0 {
                    v_a_6457_ = crate::leanh::lean_ctor_get(v___x_6456_, 0);
                    crate::leanh::lean_inc(v_a_6457_);
                    crate::leanh::lean_dec_ref_known(v___x_6456_, 1);
                    v_body_6458_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6451_);
                    crate::leanh::lean_dec(v_stx_6119_);
                    crate::leanh::lean_inc(v_body_6458_);
                    v___x_6459_ = l_Lean_Elab_Do_inferControlInfoSeq(
                        v_body_6458_,
                        v___y_6412_,
                        v___y_6413_,
                        v___y_6414_,
                        v___y_6415_,
                        v___y_6416_,
                        v___y_6417_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6459_) == 0 {
                        v_a_6460_ = crate::leanh::lean_ctor_get(v___x_6459_, 0);
                        crate::leanh::lean_inc(v_a_6460_);
                        crate::leanh::lean_dec_ref_known(v___x_6459_, 1);
                        v___x_6461_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_6411_);
                        if crate::leanh::lean_obj_tag(v___x_6461_) == 0 {
                            v_a_6462_ = crate::leanh::lean_ctor_get(v___x_6461_, 0);
                            crate::leanh::lean_inc(v_a_6462_);
                            crate::leanh::lean_dec_ref_known(v___x_6461_, 1);
                            v___x_6463_ = l_Lean_Elab_Do_elabDoFor___closed__16;
                            v___x_6464_ =
                                l_Lean_Core_mkFreshUserName(v___x_6463_, v___y_6416_, v___y_6417_);
                            if crate::leanh::lean_obj_tag(v___x_6464_) == 0 {
                                v_a_6465_ = crate::leanh::lean_ctor_get(v___x_6464_, 0);
                                crate::leanh::lean_inc(v_a_6465_);
                                crate::leanh::lean_dec_ref_known(v___x_6464_, 1);
                                v_monadInfo_6466_ = crate::leanh::lean_ctor_get(v___y_6411_, 0);
                                v_mutVars_6467_ = crate::leanh::lean_ctor_get(v___y_6411_, 1);
                                crate::leanh::lean_inc(v_a_6437_);
                                v___f_6468_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    10,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_6468_, 0, v_a_6437_);
                                crate::leanh::lean_inc_ref(v___f_6468_);
                                crate::leanh::lean_inc(v_x_6418_);
                                v___f_6469_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__2___boxed
                                        as *mut core::ffi::c_void,
                                    5,
                                    3,
                                );
                                crate::leanh::lean_closure_set(v___f_6469_, 0, v_x_6418_);
                                crate::leanh::lean_closure_set(v___f_6469_, 1, v___f_6468_);
                                crate::leanh::lean_closure_set(v___f_6469_, 2, v___x_6132_);
                                v___x_6470_ = crate::leanh::lean_box((v___x_6139_) as usize);
                                crate::leanh::lean_inc(v_a_6462_);
                                v___f_6471_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                crate::leanh::lean_closure_set(v___f_6471_, 0, v_a_6462_);
                                crate::leanh::lean_closure_set(v___f_6471_, 1, v___x_6132_);
                                crate::leanh::lean_closure_set(v___f_6471_, 2, v___x_6470_);
                                v___x_6472_ = lean_array_get_size(v_mutVars_6467_);
                                v___x_6473_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                                v___x_6474_ = lean_nat_dec_lt(v___x_6136_, v___x_6472_);
                                if v___x_6474_ == 0 {
                                    crate::leanh::lean_inc(v_x_6418_);
                                    crate::leanh::lean_inc(v_a_6447_);
                                    crate::leanh::lean_inc(v_a_6430_);
                                    crate::leanh::lean_inc(v_a_6465_);
                                    crate::leanh::lean_inc(v_a_6428_);
                                    crate::leanh::lean_inc(v_a_6457_);
                                    crate::leanh::lean_inc(v_h_x3f_6410_);
                                    crate::leanh::lean_inc(v_a_6437_);
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
                                            crate::leanh::lean_inc(v_x_6418_);
                                            crate::leanh::lean_inc(v_a_6447_);
                                            crate::leanh::lean_inc(v_a_6430_);
                                            crate::leanh::lean_inc(v_a_6465_);
                                            crate::leanh::lean_inc(v_a_6428_);
                                            crate::leanh::lean_inc(v_a_6457_);
                                            crate::leanh::lean_inc(v_h_x3f_6410_);
                                            crate::leanh::lean_inc(v_a_6437_);
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
                                            crate::leanh::lean_inc(v_x_6418_);
                                            crate::leanh::lean_inc(v_a_6447_);
                                            crate::leanh::lean_inc(v_a_6430_);
                                            crate::leanh::lean_inc(v_a_6465_);
                                            crate::leanh::lean_inc(v_a_6428_);
                                            crate::leanh::lean_inc(v_a_6457_);
                                            crate::leanh::lean_inc(v_h_x3f_6410_);
                                            crate::leanh::lean_inc(v_a_6437_);
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
                                        crate::leanh::lean_inc(v_x_6418_);
                                        crate::leanh::lean_inc(v_a_6447_);
                                        crate::leanh::lean_inc(v_a_6430_);
                                        crate::leanh::lean_inc(v_a_6465_);
                                        crate::leanh::lean_inc(v_a_6428_);
                                        crate::leanh::lean_inc(v_a_6457_);
                                        crate::leanh::lean_inc(v_h_x3f_6410_);
                                        crate::leanh::lean_inc(v_a_6437_);
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
                                crate::leanh::lean_dec(v_a_6462_);
                                crate::leanh::lean_dec(v_a_6460_);
                                crate::leanh::lean_dec(v_body_6458_);
                                crate::leanh::lean_dec(v_a_6457_);
                                crate::leanh::lean_dec(v_a_6447_);
                                crate::leanh::lean_dec(v_a_6437_);
                                crate::leanh::lean_dec(v_a_6430_);
                                crate::leanh::lean_dec(v_a_6428_);
                                crate::leanh::lean_dec(v_a_6423_);
                                crate::leanh::lean_dec(v_x_6418_);
                                crate::leanh::lean_dec(v_h_x3f_6410_);
                                v_a_6482_ = crate::leanh::lean_ctor_get(v___x_6464_, 0);
                                v_isSharedCheck_6489_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6464_)) as u8;
                                if v_isSharedCheck_6489_ == 0 {
                                    v___x_6484_ = v___x_6464_;
                                    v_isShared_6485_ = v_isSharedCheck_6489_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6482_);
                                    crate::leanh::lean_dec(v___x_6464_);
                                    v___x_6484_ = crate::leanh::lean_box(0);
                                    v_isShared_6485_ = v_isSharedCheck_6489_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6460_);
                            crate::leanh::lean_dec(v_body_6458_);
                            crate::leanh::lean_dec(v_a_6457_);
                            crate::leanh::lean_dec(v_a_6447_);
                            crate::leanh::lean_dec(v_a_6437_);
                            crate::leanh::lean_dec(v_a_6430_);
                            crate::leanh::lean_dec(v_a_6428_);
                            crate::leanh::lean_dec(v_a_6423_);
                            crate::leanh::lean_dec(v_x_6418_);
                            crate::leanh::lean_dec(v_h_x3f_6410_);
                            v_a_6490_ = crate::leanh::lean_ctor_get(v___x_6461_, 0);
                            v_isSharedCheck_6497_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6461_)) as u8;
                            if v_isSharedCheck_6497_ == 0 {
                                v___x_6492_ = v___x_6461_;
                                v_isShared_6493_ = v_isSharedCheck_6497_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6490_);
                                crate::leanh::lean_dec(v___x_6461_);
                                v___x_6492_ = crate::leanh::lean_box(0);
                                v_isShared_6493_ = v_isSharedCheck_6497_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_body_6458_);
                        crate::leanh::lean_dec(v_a_6457_);
                        crate::leanh::lean_dec(v_a_6447_);
                        crate::leanh::lean_dec(v_a_6437_);
                        crate::leanh::lean_dec(v_a_6430_);
                        crate::leanh::lean_dec(v_a_6428_);
                        crate::leanh::lean_dec(v_a_6423_);
                        crate::leanh::lean_dec(v_x_6418_);
                        crate::leanh::lean_dec(v_h_x3f_6410_);
                        v_a_6498_ = crate::leanh::lean_ctor_get(v___x_6459_, 0);
                        v_isSharedCheck_6505_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6459_)) as u8;
                        if v_isSharedCheck_6505_ == 0 {
                            v___x_6500_ = v___x_6459_;
                            v_isShared_6501_ = v_isSharedCheck_6505_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6498_);
                            crate::leanh::lean_dec(v___x_6459_);
                            v___x_6500_ = crate::leanh::lean_box(0);
                            v_isShared_6501_ = v_isSharedCheck_6505_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6447_);
                    crate::leanh::lean_dec(v_a_6437_);
                    crate::leanh::lean_dec(v_a_6430_);
                    crate::leanh::lean_dec(v_a_6428_);
                    crate::leanh::lean_dec(v_a_6423_);
                    crate::leanh::lean_dec(v_x_6418_);
                    crate::leanh::lean_dec(v_h_x3f_6410_);
                    crate::leanh::lean_dec(v_stx_6119_);
                    return v___x_6456_;
                }
            }
            22 => {
                if v_isShared_6485_ == 0 {
                    v___x_6487_ = v___x_6484_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_a_6482_);
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
                    v_reuseFailAlloc_6496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_a_6490_);
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
                    v_reuseFailAlloc_6504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
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
                    v_reuseFailAlloc_6516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6516_, 0, v_a_6510_);
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
                    v_reuseFailAlloc_6524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_a_6518_);
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
                    v_reuseFailAlloc_6532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
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
                    v_reuseFailAlloc_6540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
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
    mut v_stx_6550_: *mut crate::leanh::LeanObject,
    mut v_dec_6551_: *mut crate::leanh::LeanObject,
    mut v_a_6552_: *mut crate::leanh::LeanObject,
    mut v_a_6553_: *mut crate::leanh::LeanObject,
    mut v_a_6554_: *mut crate::leanh::LeanObject,
    mut v_a_6555_: *mut crate::leanh::LeanObject,
    mut v_a_6556_: *mut crate::leanh::LeanObject,
    mut v_a_6557_: *mut crate::leanh::LeanObject,
    mut v_a_6558_: *mut crate::leanh::LeanObject,
    mut v_a_6559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_6558_);
    crate::leanh::lean_dec_ref(v_a_6557_);
    crate::leanh::lean_dec(v_a_6556_);
    crate::leanh::lean_dec_ref(v_a_6555_);
    crate::leanh::lean_dec(v_a_6554_);
    crate::leanh::lean_dec_ref(v_a_6553_);
    crate::leanh::lean_dec_ref(v_a_6552_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(
    mut v_00_u03b1_6561_: *mut crate::leanh::LeanObject,
    mut v_msg_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
    mut v___y_6567_: *mut crate::leanh::LeanObject,
    mut v___y_6568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6571_: *mut crate::leanh::LeanObject,
    mut v_msg_6572_: *mut crate::leanh::LeanObject,
    mut v___y_6573_: *mut crate::leanh::LeanObject,
    mut v___y_6574_: *mut crate::leanh::LeanObject,
    mut v___y_6575_: *mut crate::leanh::LeanObject,
    mut v___y_6576_: *mut crate::leanh::LeanObject,
    mut v___y_6577_: *mut crate::leanh::LeanObject,
    mut v___y_6578_: *mut crate::leanh::LeanObject,
    mut v___y_6579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_6578_);
    crate::leanh::lean_dec_ref(v___y_6577_);
    crate::leanh::lean_dec(v___y_6576_);
    crate::leanh::lean_dec_ref(v___y_6575_);
    crate::leanh::lean_dec(v___y_6574_);
    crate::leanh::lean_dec_ref(v___y_6573_);
    return v_res_6580_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(
    mut v_00_u03b1_6581_: *mut crate::leanh::LeanObject,
    mut v_name_6582_: *mut crate::leanh::LeanObject,
    mut v_type_6583_: *mut crate::leanh::LeanObject,
    mut v_k_6584_: *mut crate::leanh::LeanObject,
    mut v___y_6585_: *mut crate::leanh::LeanObject,
    mut v___y_6586_: *mut crate::leanh::LeanObject,
    mut v___y_6587_: *mut crate::leanh::LeanObject,
    mut v___y_6588_: *mut crate::leanh::LeanObject,
    mut v___y_6589_: *mut crate::leanh::LeanObject,
    mut v___y_6590_: *mut crate::leanh::LeanObject,
    mut v___y_6591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6594_: *mut crate::leanh::LeanObject,
    mut v_name_6595_: *mut crate::leanh::LeanObject,
    mut v_type_6596_: *mut crate::leanh::LeanObject,
    mut v_k_6597_: *mut crate::leanh::LeanObject,
    mut v___y_6598_: *mut crate::leanh::LeanObject,
    mut v___y_6599_: *mut crate::leanh::LeanObject,
    mut v___y_6600_: *mut crate::leanh::LeanObject,
    mut v___y_6601_: *mut crate::leanh::LeanObject,
    mut v___y_6602_: *mut crate::leanh::LeanObject,
    mut v___y_6603_: *mut crate::leanh::LeanObject,
    mut v___y_6604_: *mut crate::leanh::LeanObject,
    mut v___y_6605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_6604_);
    crate::leanh::lean_dec_ref(v___y_6603_);
    crate::leanh::lean_dec(v___y_6602_);
    crate::leanh::lean_dec_ref(v___y_6601_);
    crate::leanh::lean_dec(v___y_6600_);
    crate::leanh::lean_dec_ref(v___y_6599_);
    crate::leanh::lean_dec_ref(v___y_6598_);
    return v_res_6606_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(
    mut v_msgData_6607_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6608_: *mut crate::leanh::LeanObject,
    mut v___y_6609_: *mut crate::leanh::LeanObject,
    mut v___y_6610_: *mut crate::leanh::LeanObject,
    mut v___y_6611_: *mut crate::leanh::LeanObject,
    mut v___y_6612_: *mut crate::leanh::LeanObject,
    mut v___y_6613_: *mut crate::leanh::LeanObject,
    mut v___y_6614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6616_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_6607_, v_macroStack_6608_, v___y_6613_);
    return v___x_6616_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(
    mut v_msgData_6617_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6618_: *mut crate::leanh::LeanObject,
    mut v___y_6619_: *mut crate::leanh::LeanObject,
    mut v___y_6620_: *mut crate::leanh::LeanObject,
    mut v___y_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
    mut v___y_6624_: *mut crate::leanh::LeanObject,
    mut v___y_6625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6626_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_6617_, v_macroStack_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
    crate::leanh::lean_dec(v___y_6624_);
    crate::leanh::lean_dec_ref(v___y_6623_);
    crate::leanh::lean_dec(v___y_6622_);
    crate::leanh::lean_dec_ref(v___y_6621_);
    crate::leanh::lean_dec(v___y_6620_);
    crate::leanh::lean_dec_ref(v___y_6619_);
    return v_res_6626_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6634_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_6635_ = l_Lean_Elab_Do_expandDoFor___closed__1;
    v___x_6636_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1;
    v___x_6637_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_6639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6640_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
    return v_res_6640_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_For(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_For(
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
pub unsafe fn initialize_Lean_Elab_BuiltinDo_For(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_ProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_For(builtin);
}
