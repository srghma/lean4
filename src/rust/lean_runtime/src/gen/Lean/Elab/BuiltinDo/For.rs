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
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_Pi_instInhabited___redArg___lam__0,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
use crate::r#gen::Lean::Parser::Do::{initialize_Lean_Parser_Do, meta_initialize_Lean_Parser_Do};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_8, lean_apply_9, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [83, 116, 100, 46, 116, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut LeanObject,13215525487457488549 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value) as *mut LeanObject,7754083906429771139 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut LeanObject,13029182796945285130 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 95, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value) as *mut LeanObject,16096857990383608286 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 111, 76, 101, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 77, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 116, 100, 46, 83, 116, 114, 101, 97, 109, 46, 110, 101, 120, 116, 63, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 101, 120, 116, 63, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value) as *mut LeanObject,17138251589876785539 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value) as *mut LeanObject,3899314177519732191 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut LeanObject,17416048715816169289 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut LeanObject,18184376426117065311 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut LeanObject,9480010471355609749 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 66, 114, 101, 97, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 114, 101, 97, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut LeanObject,15308379890181982757 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut LeanObject,18184376426117065311 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut LeanObject,4893146552088433753 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [115, 39, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value) as *mut LeanObject,6632439502835183307 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 82, 101, 97, 115, 115, 105, 103, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 78, 111, 66, 105, 110, 100, 101, 114, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 78, 101, 115, 116, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [84, 104, 101, 32, 112, 114, 111, 111, 102, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 104, 101, 114, 101, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101, 110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 32, 121, 101, 116, 46, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 70, 111, 114, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value) as *mut LeanObject,9513652089846993813 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__0_value) as *mut LeanObject,
        16953626593407929508 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_expandDoFor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value) as *mut LeanObject,4570674678924417756 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__6_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__7_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__8_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__9_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__9_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value) as *mut LeanObject,4365236509002904093 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value) as *mut LeanObject,9383794970646754147 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value) as *mut LeanObject,13242179749370575553 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value) as *mut LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value) as *mut LeanObject,16529391333736644786 as *mut LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__15_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_expandDoFor___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__15_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__15_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_expandDoFor___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut LeanObject,102172329646148436 as *mut LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value) as *mut LeanObject,18312965975140834652 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value)
                as *mut LeanObject,
            9833841078580172006 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value)
                as *mut LeanObject,
            565778312915565143 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value: LeanStringObject<44> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value: LeanStringObject<17> =
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
            69, 97, 114, 108, 121, 32, 114, 101, 116, 117, 114, 110, 105, 110, 103, 32, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value: LeanStringObject<6> =
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
        m_data: [121, 105, 101, 108, 100, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value)
                as *mut LeanObject,
            8016886460890159001 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__8___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value)
                as *mut LeanObject,
            2981963283782553289 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value) as *mut LeanObject,13286986945483979944 as *mut LeanObject] };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value: LeanStringObject<6> =
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
        m_data: [66, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value: LeanStringObject<8> =
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
        m_data: [109, 97, 116, 99, 104, 95, 49, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value)
                as *mut LeanObject,
            10906666425700568089 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value)
                as *mut LeanObject,
            2052082663577137876 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value)
                as *mut LeanObject,
            12942615993048023751 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value)
                as *mut LeanObject,
            15289851429949568889 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value)
                as *mut LeanObject,
            8286241746160725162 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value: LeanStringObject<11> =
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
        m_data: [77, 101, 109, 98, 101, 114, 115, 104, 105, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
                as *mut LeanObject,
            7877420268164864461 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value)
                as *mut LeanObject,
            5015202941514963680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value) as *mut LeanObject,
        11398022837381273823 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value) as *mut LeanObject,
        11398022837381273823 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Do_elabDoFor___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__2_value) as *mut LeanObject,
        6704322920896662537 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
            as *mut LeanObject,
        7877420268164864461 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__5_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__5_value) as *mut LeanObject,
        16646031496814324272 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__7_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value) as *mut LeanObject,
        8702119947958352715 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__9_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__9_value) as *mut LeanObject;
static l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value) as *mut LeanObject,
        8702119947958352715 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Do_elabDoFor___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__9_value) as *mut LeanObject,
        6740408439742725642 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__10_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__11_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__11_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__11_value) as *mut LeanObject,
        988715873908496486 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__12_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__13_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__13_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__13_value) as *mut LeanObject,
        17734088147927324564 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__14_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__15_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Do_elabDoFor___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__15_value) as *mut LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__15_value) as *mut LeanObject,
        6333055220850301478 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Do_elabDoFor___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 68, 111, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut LeanObject,102172329646148436 as *mut LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value) as *mut LeanObject,13250242672952379177 as *mut LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_macroScope_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v_quotContext_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_3326_ = lean_ctor_get(v___y_3325_, 0);
                v_traceMsgs_3327_ = lean_ctor_get(v___y_3325_, 1);
                v_expandedMacroDecls_3328_ = lean_ctor_get(v___y_3325_, 2);
                v_isSharedCheck_3341_ = (!lean_is_exclusive(v___y_3325_)) as u8;
                if v_isSharedCheck_3341_ == 0 {
                    v___x_3330_ = v___y_3325_;
                    v_isShared_3331_ = v_isSharedCheck_3341_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_3328_);
                    lean_inc(v_traceMsgs_3327_);
                    lean_inc(v_macroScope_3326_);
                    lean_dec(v___y_3325_);
                    v___x_3330_ = lean_box(0);
                    v_isShared_3331_ = v_isSharedCheck_3341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_quotContext_3332_ = lean_ctor_get(v___y_3324_, 1);
                v___x_3333_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1;
                v___x_3334_ = lean_unsigned_to_nat(1);
                v___x_3335_ = lean_nat_add(v_macroScope_3326_, v___x_3334_);
                if v_isShared_3331_ == 0 {
                    lean_ctor_set(v___x_3330_, 0, v___x_3335_);
                    v___x_3337_ = v___x_3330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3335_);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_traceMsgs_3327_);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_expandedMacroDecls_3328_);
                    v___x_3337_ = v_reuseFailAlloc_3340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_quotContext_3332_);
                v___x_3338_ =
                    l_Lean_addMacroScope(v_quotContext_3332_, v___x_3333_, v_macroScope_3326_);
                v___x_3339_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3339_, 0, v___x_3338_);
                lean_ctor_set(v___x_3339_, 1, v___x_3337_);
                return v___x_3339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3344_: *mut LeanObject = core::ptr::null_mut();
    v_res_3344_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_3342_, v___y_3343_);
    lean_dec_ref(v___y_3342_);
    return v_res_3344_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
    mut v_ref_3345_: *mut LeanObject,
    mut v_canonical_3346_: u8,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3349_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_3347_, v___y_3348_);
                v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
                v_a_3351_ = lean_ctor_get(v___x_3349_, 1);
                v_isSharedCheck_3359_ = (!lean_is_exclusive(v___x_3349_)) as u8;
                if v_isSharedCheck_3359_ == 0 {
                    v___x_3353_ = v___x_3349_;
                    v_isShared_3354_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3351_);
                    lean_inc(v_a_3350_);
                    lean_dec(v___x_3349_);
                    v___x_3353_ = lean_box(0);
                    v_isShared_3354_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3355_ = l_Lean_mkIdentFrom(v_ref_3345_, v_a_3350_, v_canonical_3346_);
                if v_isShared_3354_ == 0 {
                    lean_ctor_set(v___x_3353_, 0, v___x_3355_);
                    v___x_3357_ = v___x_3353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
                    lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_a_3351_);
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
    mut v_ref_3360_: *mut LeanObject,
    mut v_canonical_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonical_boxed_3364_: u8 = 0;
    let mut v_res_3365_: *mut LeanObject = core::ptr::null_mut();
    v_canonical_boxed_3364_ = (lean_unbox(v_canonical_3361_) as u8);
    v_res_3365_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
        v_ref_3360_,
        v_canonical_boxed_3364_,
        v___y_3362_,
        v___y_3363_,
    );
    lean_dec_ref(v___y_3362_);
    lean_dec(v_ref_3360_);
    return v_res_3365_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    v___x_3370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3;
    v___x_3371_ = l_String_toRawSubstring_x27(v___x_3370_);
    return v___x_3371_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23()
-> *mut LeanObject {
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Array_mkArray0(lean_box(0));
    return v___x_3401_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33()
-> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32;
    v___x_3412_ = l_String_toRawSubstring_x27(v___x_3411_);
    return v___x_3412_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44()
-> *mut LeanObject {
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    v___x_3430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43;
    v___x_3431_ = l_String_toRawSubstring_x27(v___x_3430_);
    return v___x_3431_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54()
-> *mut LeanObject {
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v___x_3448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53;
    v___x_3449_ = l_String_toRawSubstring_x27(v___x_3448_);
    return v___x_3449_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65()
-> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64;
    v___x_3469_ = l_String_toRawSubstring_x27(v___x_3468_);
    return v___x_3469_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70()
-> *mut LeanObject {
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69;
    v___x_3475_ = l_String_toRawSubstring_x27(v___x_3474_);
    return v___x_3475_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(
    mut v___x_3484_: *mut LeanObject,
    mut v___x_3485_: *mut LeanObject,
    mut v___x_3486_: *mut LeanObject,
    mut v___x_3487_: u8,
    mut v___x_3488_: *mut LeanObject,
    mut v___x_3489_: *mut LeanObject,
    mut v___x_3490_: *mut LeanObject,
    mut v___f_3491_: *mut LeanObject,
    mut v_fst_3492_: *mut LeanObject,
    mut v___x_3493_: *mut LeanObject,
    mut v_snd_3494_: *mut LeanObject,
    mut v_x_3495_: *mut LeanObject,
    mut v_h_x3f_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v_a_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_reuseFailAlloc_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_val_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3499_ = l_Lean_Syntax_getArg(v___x_3484_, v___x_3485_);
                v___x_3500_ = l_Lean_Syntax_getArg(v___x_3484_, v___x_3486_);
                if lean_obj_tag(v_h_x3f_3496_) == 1 {
                    v_val_3720_ = lean_ctor_get(v_h_x3f_3496_, 0);
                    v___x_3721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77;
                    v___x_3722_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_val_3720_,
                        v___x_3721_,
                        v___y_3497_,
                        v___y_3498_,
                    );
                    if lean_obj_tag(v___x_3722_) == 0 {
                        v_a_3723_ = lean_ctor_get(v___x_3722_, 1);
                        lean_inc(v_a_3723_);
                        lean_dec_ref_known(v___x_3722_, 2);
                        v___y_3502_ = v_a_3723_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3500_);
                        lean_dec(v___x_3499_);
                        lean_dec(v_snd_3494_);
                        lean_dec_ref(v___x_3493_);
                        lean_dec(v_fst_3492_);
                        lean_dec_ref(v___f_3491_);
                        lean_dec_ref(v___x_3490_);
                        lean_dec_ref(v___x_3489_);
                        lean_dec_ref(v___x_3488_);
                        v_a_3724_ = lean_ctor_get(v___x_3722_, 0);
                        v_a_3725_ = lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3732_ = (!lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3732_ == 0 {
                            v___x_3727_ = v___x_3722_;
                            v_isShared_3728_ = v_isSharedCheck_3732_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3725_);
                            lean_inc(v_a_3724_);
                            lean_dec(v___x_3722_);
                            v___x_3727_ = lean_box(0);
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
                v_quotContext_3503_ = lean_ctor_get(v___y_3497_, 1);
                v_currMacroScope_3504_ = lean_ctor_get(v___y_3497_, 2);
                v_ref_3505_ = lean_ctor_get(v___y_3497_, 5);
                v_ref_3506_ = l_Lean_replaceRef(v___x_3500_, v_ref_3505_);
                v___x_3507_ = l_Lean_SourceInfo_fromRef(v_ref_3506_, v___x_3487_);
                lean_dec(v_ref_3506_);
                v___x_3508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0;
                lean_inc_ref_n(v___x_3490_, 3);
                lean_inc_ref_n(v___x_3489_, 3);
                lean_inc_ref_n(v___x_3488_, 3);
                v___x_3509_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3508_);
                v___x_3510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1;
                v___x_3511_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3510_);
                v___x_3512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2;
                lean_inc_n(v___x_3507_, 6);
                v___x_3513_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3513_, 0, v___x_3507_);
                lean_ctor_set(v___x_3513_, 1, v___x_3512_);
                v___x_3514_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
                v___x_3515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7;
                lean_inc(v_currMacroScope_3504_);
                lean_inc(v_quotContext_3503_);
                v___x_3516_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3515_, v_currMacroScope_3504_);
                v___x_3517_ = lean_box(0);
                v___x_3518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11;
                v___x_3519_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3519_, 0, v___x_3507_);
                lean_ctor_set(v___x_3519_, 1, v___x_3514_);
                lean_ctor_set(v___x_3519_, 2, v___x_3516_);
                lean_ctor_set(v___x_3519_, 3, v___x_3518_);
                lean_inc(v___x_3511_);
                v___x_3520_ =
                    l_Lean_Syntax_node2(v___x_3507_, v___x_3511_, v___x_3513_, v___x_3519_);
                v___x_3521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_3522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14;
                v___x_3523_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3522_);
                v___x_3524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15;
                v___x_3525_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3525_, 0, v___x_3507_);
                lean_ctor_set(v___x_3525_, 1, v___x_3524_);
                lean_inc(v___x_3523_);
                v___x_3526_ = l_Lean_Syntax_node1(v___x_3507_, v___x_3523_, v___x_3525_);
                lean_inc(v___x_3500_);
                lean_inc_n(v___x_3526_, 2);
                v___x_3527_ = l_Lean_Syntax_node4(
                    v___x_3507_,
                    v___x_3521_,
                    v___x_3526_,
                    v___x_3526_,
                    v___x_3526_,
                    v___x_3500_,
                );
                v_macroScope_3528_ = lean_ctor_get(v___y_3502_, 0);
                v_traceMsgs_3529_ = lean_ctor_get(v___y_3502_, 1);
                v_expandedMacroDecls_3530_ = lean_ctor_get(v___y_3502_, 2);
                v_isSharedCheck_3719_ = (!lean_is_exclusive(v___y_3502_)) as u8;
                if v_isSharedCheck_3719_ == 0 {
                    v___x_3532_ = v___y_3502_;
                    v_isShared_3533_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_3530_);
                    lean_inc(v_traceMsgs_3529_);
                    lean_inc(v_macroScope_3528_);
                    lean_dec(v___y_3502_);
                    v___x_3532_ = lean_box(0);
                    v_isShared_3533_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3534_ = lean_nat_add(v_macroScope_3528_, v___x_3485_);
                if v_isShared_3533_ == 0 {
                    lean_ctor_set(v___x_3532_, 0, v___x_3534_);
                    v___x_3536_ = v___x_3532_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3534_);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_traceMsgs_3529_);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_expandedMacroDecls_3530_);
                    v___x_3536_ = v_reuseFailAlloc_3718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___f_3491_);
                lean_inc_ref(v___y_3497_);
                lean_inc(v_ref_3505_);
                v___x_3537_ = lean_apply_3(v___f_3491_, v_ref_3505_, v___y_3497_, v___x_3536_);
                if lean_obj_tag(v___x_3537_) == 0 {
                    v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
                    lean_inc_n(v_a_3538_, 9);
                    v_a_3539_ = lean_ctor_get(v___x_3537_, 1);
                    lean_inc(v_a_3539_);
                    lean_dec_ref_known(v___x_3537_, 2);
                    lean_inc(v___x_3509_);
                    v___x_3540_ =
                        l_Lean_Syntax_node2(v___x_3507_, v___x_3509_, v___x_3520_, v___x_3527_);
                    v___x_3541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17;
                    lean_inc(v_quotContext_3503_);
                    v___x_3542_ =
                        l_Lean_addMacroScope(v_quotContext_3503_, v___x_3541_, v_macroScope_3528_);
                    v___x_3543_ = l_Lean_mkIdentFrom(v___x_3500_, v___x_3542_, v___x_3487_);
                    lean_dec(v___x_3500_);
                    v___x_3544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18;
                    lean_inc_ref_n(v___x_3490_, 6);
                    lean_inc_ref_n(v___x_3489_, 6);
                    lean_inc_ref_n(v___x_3488_, 6);
                    v___x_3545_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3544_);
                    v___x_3546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19;
                    v___x_3547_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3546_);
                    v___x_3548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20;
                    v___x_3549_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3549_, 0, v_a_3538_);
                    lean_ctor_set(v___x_3549_, 1, v___x_3548_);
                    v___x_3550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21;
                    v___x_3551_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3551_, 0, v_a_3538_);
                    lean_ctor_set(v___x_3551_, 1, v___x_3550_);
                    v___x_3552_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3521_, v___x_3551_);
                    v___x_3553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22;
                    v___x_3554_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3553_);
                    v___x_3555_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                    v___x_3556_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3556_, 0, v_a_3538_);
                    lean_ctor_set(v___x_3556_, 1, v___x_3521_);
                    lean_ctor_set(v___x_3556_, 2, v___x_3555_);
                    lean_inc_ref_n(v___x_3556_, 3);
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
                    lean_inc(v___x_3543_);
                    lean_inc(v___x_3563_);
                    v___x_3564_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3563_, v___x_3543_);
                    v___x_3565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27;
                    v___x_3566_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3566_, 0, v_a_3538_);
                    lean_ctor_set(v___x_3566_, 1, v___x_3565_);
                    v___x_3567_ = l_Lean_Syntax_node5(
                        v_a_3538_,
                        v___x_3561_,
                        v___x_3564_,
                        v___x_3556_,
                        v___x_3556_,
                        v___x_3566_,
                        v___x_3540_,
                    );
                    lean_inc_ref(v___y_3497_);
                    lean_inc(v_ref_3505_);
                    v___x_3568_ = lean_apply_3(v___f_3491_, v_ref_3505_, v___y_3497_, v_a_3539_);
                    if lean_obj_tag(v___x_3568_) == 0 {
                        v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
                        v_a_3570_ = lean_ctor_get(v___x_3568_, 1);
                        v_isSharedCheck_3699_ = (!lean_is_exclusive(v___x_3568_)) as u8;
                        if v_isSharedCheck_3699_ == 0 {
                            v___x_3572_ = v___x_3568_;
                            v_isShared_3573_ = v_isSharedCheck_3699_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3570_);
                            lean_inc(v_a_3569_);
                            lean_dec(v___x_3568_);
                            v___x_3572_ = lean_box(0);
                            v_isShared_3573_ = v_isSharedCheck_3699_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3567_);
                        lean_dec(v___x_3563_);
                        lean_dec(v___x_3559_);
                        lean_dec(v___x_3557_);
                        lean_dec_ref_known(v___x_3556_, 3);
                        lean_dec(v___x_3552_);
                        lean_dec_ref_known(v___x_3549_, 2);
                        lean_dec(v___x_3547_);
                        lean_dec(v___x_3545_);
                        lean_dec(v___x_3543_);
                        lean_dec(v_a_3538_);
                        lean_dec(v___x_3523_);
                        lean_dec(v___x_3511_);
                        lean_dec(v___x_3509_);
                        lean_dec(v___x_3499_);
                        lean_dec(v_snd_3494_);
                        lean_dec_ref(v___x_3493_);
                        lean_dec(v_fst_3492_);
                        lean_dec_ref(v___x_3490_);
                        lean_dec_ref(v___x_3489_);
                        lean_dec_ref(v___x_3488_);
                        v_a_3700_ = lean_ctor_get(v___x_3568_, 0);
                        v_a_3701_ = lean_ctor_get(v___x_3568_, 1);
                        v_isSharedCheck_3708_ = (!lean_is_exclusive(v___x_3568_)) as u8;
                        if v_isSharedCheck_3708_ == 0 {
                            v___x_3703_ = v___x_3568_;
                            v_isShared_3704_ = v_isSharedCheck_3708_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3701_);
                            lean_inc(v_a_3700_);
                            lean_dec(v___x_3568_);
                            v___x_3703_ = lean_box(0);
                            v_isShared_3704_ = v_isSharedCheck_3708_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_macroScope_3528_);
                    lean_dec(v___x_3527_);
                    lean_dec(v___x_3523_);
                    lean_dec(v___x_3520_);
                    lean_dec(v___x_3511_);
                    lean_dec(v___x_3509_);
                    lean_dec(v___x_3507_);
                    lean_dec(v___x_3500_);
                    lean_dec(v___x_3499_);
                    lean_dec(v_snd_3494_);
                    lean_dec_ref(v___x_3493_);
                    lean_dec(v_fst_3492_);
                    lean_dec_ref(v___f_3491_);
                    lean_dec_ref(v___x_3490_);
                    lean_dec_ref(v___x_3489_);
                    lean_dec_ref(v___x_3488_);
                    v_a_3709_ = lean_ctor_get(v___x_3537_, 0);
                    v_a_3710_ = lean_ctor_get(v___x_3537_, 1);
                    v_isSharedCheck_3717_ = (!lean_is_exclusive(v___x_3537_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3712_ = v___x_3537_;
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3710_);
                        lean_inc(v_a_3709_);
                        lean_dec(v___x_3537_);
                        v___x_3712_ = lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_n(v_a_3538_, 2);
                v___x_3574_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3559_, v___x_3567_);
                v___x_3575_ = l_Lean_Syntax_node4(
                    v_a_3538_,
                    v___x_3547_,
                    v___x_3549_,
                    v___x_3552_,
                    v___x_3557_,
                    v___x_3574_,
                );
                lean_inc_n(v___x_3545_, 4);
                v___x_3576_ = l_Lean_Syntax_node2(v_a_3538_, v___x_3545_, v___x_3575_, v___x_3556_);
                v___x_3577_ = lean_array_push(v_fst_3492_, v___x_3576_);
                v___x_3578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28;
                lean_inc_ref_n(v___x_3490_, 11);
                lean_inc_ref_n(v___x_3489_, 11);
                lean_inc_ref_n(v___x_3488_, 13);
                v___x_3579_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3578_);
                v___x_3580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29;
                v___x_3581_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3580_);
                v___x_3582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                lean_inc_n(v_a_3569_, 54);
                v___x_3583_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3583_, 0, v_a_3569_);
                lean_ctor_set(v___x_3583_, 1, v___x_3582_);
                v___x_3584_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3584_, 0, v_a_3569_);
                lean_ctor_set(v___x_3584_, 1, v___x_3521_);
                lean_ctor_set(v___x_3584_, 2, v___x_3555_);
                v___x_3585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31;
                v___x_3586_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3585_);
                v___x_3587_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3587_, 0, v_a_3569_);
                lean_ctor_set(v___x_3587_, 1, v___x_3512_);
                v___x_3588_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
                v___x_3589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36;
                lean_inc_n(v_currMacroScope_3504_, 5);
                lean_inc_n(v_quotContext_3503_, 5);
                v___x_3590_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3589_, v_currMacroScope_3504_);
                v___x_3591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38;
                v___x_3592_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3592_, 0, v_a_3569_);
                lean_ctor_set(v___x_3592_, 1, v___x_3588_);
                lean_ctor_set(v___x_3592_, 2, v___x_3590_);
                lean_ctor_set(v___x_3592_, 3, v___x_3591_);
                v___x_3593_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3511_, v___x_3587_, v___x_3592_);
                v___x_3594_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3594_, 0, v_a_3569_);
                lean_ctor_set(v___x_3594_, 1, v___x_3524_);
                v___x_3595_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3523_, v___x_3594_);
                lean_inc(v___x_3543_);
                lean_inc_n(v___x_3595_, 2);
                v___x_3596_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3521_,
                    v___x_3595_,
                    v___x_3595_,
                    v___x_3595_,
                    v___x_3543_,
                );
                lean_inc(v___x_3509_);
                v___x_3597_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3509_, v___x_3593_, v___x_3596_);
                lean_inc_ref_n(v___x_3584_, 9);
                v___x_3598_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3586_, v___x_3584_, v___x_3597_);
                v___x_3599_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3598_);
                v___x_3600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                v___x_3601_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3601_, 0, v_a_3569_);
                lean_ctor_set(v___x_3601_, 1, v___x_3600_);
                v___x_3602_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40;
                v___x_3603_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3602_);
                v___x_3604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41;
                v___x_3605_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3604_);
                v___x_3606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                v___x_3607_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3607_, 0, v_a_3569_);
                lean_ctor_set(v___x_3607_, 1, v___x_3606_);
                v___x_3608_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
                v___x_3609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45;
                v___x_3610_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3609_, v_currMacroScope_3504_);
                v___x_3611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49;
                v___x_3612_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3612_, 0, v_a_3569_);
                lean_ctor_set(v___x_3612_, 1, v___x_3608_);
                lean_ctor_set(v___x_3612_, 2, v___x_3610_);
                lean_ctor_set(v___x_3612_, 3, v___x_3611_);
                v___x_3613_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3612_);
                v___x_3614_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3613_);
                v___x_3615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                v___x_3616_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3616_, 0, v_a_3569_);
                lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51;
                v___x_3618_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3617_);
                v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52;
                v___x_3620_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3620_, 0, v_a_3569_);
                lean_ctor_set(v___x_3620_, 1, v___x_3619_);
                v___x_3621_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3618_, v___x_3620_);
                v___x_3622_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3545_, v___x_3621_, v___x_3584_);
                v___x_3623_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3622_);
                lean_inc_n(v___x_3579_, 2);
                v___x_3624_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3579_, v___x_3623_);
                lean_inc_ref(v___x_3616_);
                lean_inc_ref(v___x_3607_);
                lean_inc(v___x_3605_);
                v___x_3625_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3605_,
                    v___x_3607_,
                    v___x_3614_,
                    v___x_3616_,
                    v___x_3624_,
                );
                v___x_3626_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
                v___x_3627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55;
                v___x_3628_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3627_, v_currMacroScope_3504_);
                v___x_3629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58;
                v___x_3630_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3630_, 0, v_a_3569_);
                lean_ctor_set(v___x_3630_, 1, v___x_3626_);
                lean_ctor_set(v___x_3630_, 2, v___x_3628_);
                lean_ctor_set(v___x_3630_, 3, v___x_3629_);
                v___x_3631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59;
                v___x_3632_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3631_);
                v___x_3633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60;
                v___x_3634_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3633_);
                v___x_3635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61;
                v___x_3636_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3636_, 0, v_a_3569_);
                lean_ctor_set(v___x_3636_, 1, v___x_3635_);
                v___x_3637_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63;
                v___x_3638_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
                v___x_3639_ = lean_box(0);
                v___x_3640_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3639_, v_currMacroScope_3504_);
                v___x_3641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66;
                v___x_3642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67;
                v___x_3643_ = l_Lean_Name_mkStr3(v___x_3488_, v___x_3641_, v___x_3642_);
                v___x_3644_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                v___x_3645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68;
                v___x_3646_ = l_Lean_Name_mkStr2(v___x_3488_, v___x_3645_);
                v___x_3647_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3647_, 0, v___x_3646_);
                v___x_3648_ = l_Lean_Name_mkStr3(v___x_3488_, v___x_3489_, v___x_3490_);
                v___x_3649_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3649_, 0, v___x_3648_);
                v___x_3650_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3650_, 0, v___x_3649_);
                lean_ctor_set(v___x_3650_, 1, v___x_3517_);
                v___x_3651_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3651_, 0, v___x_3647_);
                lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                v___x_3652_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3652_, 0, v___x_3644_);
                lean_ctor_set(v___x_3652_, 1, v___x_3651_);
                v___x_3653_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3653_, 0, v_a_3569_);
                lean_ctor_set(v___x_3653_, 1, v___x_3638_);
                lean_ctor_set(v___x_3653_, 2, v___x_3640_);
                lean_ctor_set(v___x_3653_, 3, v___x_3652_);
                v___x_3654_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3637_, v___x_3653_);
                v___x_3655_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3634_, v___x_3636_, v___x_3654_);
                v___x_3656_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3656_, 0, v_a_3569_);
                lean_ctor_set(v___x_3656_, 1, v___x_3493_);
                v___x_3657_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
                v___x_3658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71;
                v___x_3659_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3658_, v_currMacroScope_3504_);
                v___x_3660_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3660_, 0, v_a_3569_);
                lean_ctor_set(v___x_3660_, 1, v___x_3657_);
                lean_ctor_set(v___x_3660_, 2, v___x_3659_);
                lean_ctor_set(v___x_3660_, 3, v___x_3517_);
                lean_inc_ref(v___x_3660_);
                v___x_3661_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3660_);
                v___x_3662_ = l_Lean_Syntax_node3(
                    v_a_3569_,
                    v___x_3521_,
                    v___x_3499_,
                    v___x_3656_,
                    v___x_3661_,
                );
                v___x_3663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72;
                v___x_3664_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3664_, 0, v_a_3569_);
                lean_ctor_set(v___x_3664_, 1, v___x_3663_);
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
                v___x_3675_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3675_, 0, v_a_3569_);
                lean_ctor_set(v___x_3675_, 1, v___x_3565_);
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
                v___x_3682_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3682_, 0, v_a_3569_);
                lean_ctor_set(v___x_3682_, 1, v___x_3681_);
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
                v___x_3694_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3694_, 0, v___x_3577_);
                lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                v___x_3695_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3695_, 0, v___x_3694_);
                if v_isShared_3573_ == 0 {
                    lean_ctor_set(v___x_3572_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3572_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
                    lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_a_3570_);
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
                    v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3700_);
                    lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_a_3701_);
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
                    v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3709_);
                    lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_a_3710_);
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
                    v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3724_);
                    lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_a_3725_);
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
    mut v___x_3733_: *mut LeanObject,
    mut v___x_3734_: *mut LeanObject,
    mut v___x_3735_: *mut LeanObject,
    mut v___x_3736_: *mut LeanObject,
    mut v___x_3737_: *mut LeanObject,
    mut v___x_3738_: *mut LeanObject,
    mut v___x_3739_: *mut LeanObject,
    mut v___f_3740_: *mut LeanObject,
    mut v_fst_3741_: *mut LeanObject,
    mut v___x_3742_: *mut LeanObject,
    mut v_snd_3743_: *mut LeanObject,
    mut v_x_3744_: *mut LeanObject,
    mut v_h_x3f_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146124__boxed_3748_: u8 = 0;
    let mut v_res_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_146124__boxed_3748_ = (lean_unbox(v___x_3736_) as u8);
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
    lean_dec_ref(v___y_3746_);
    lean_dec(v_h_x3f_3745_);
    lean_dec(v___x_3735_);
    lean_dec(v___x_3734_);
    lean_dec(v___x_3733_);
    return v_res_3749_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(
    mut v___x_3750_: u8,
    mut v_____do__lift_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3751_, v___x_3750_);
    v___x_3755_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3755_, 0, v___x_3754_);
    lean_ctor_set(v___x_3755_, 1, v___y_3753_);
    return v___x_3755_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(
    mut v___x_3756_: *mut LeanObject,
    mut v_____do__lift_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146730__boxed_3760_: u8 = 0;
    let mut v_res_3761_: *mut LeanObject = core::ptr::null_mut();
    v___x_146730__boxed_3760_ = (lean_unbox(v___x_3756_) as u8);
    v_res_3761_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(
            v___x_146730__boxed_3760_,
            v_____do__lift_3757_,
            v___y_3758_,
            v___y_3759_,
        );
    lean_dec_ref(v___y_3758_);
    lean_dec(v_____do__lift_3757_);
    return v_res_3761_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
    mut v___x_3772_: u8,
    mut v_a_3773_: *mut LeanObject,
    mut v_b_3774_: *mut LeanObject,
    mut v___y_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: u8 = 0;
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v_a_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v_unused_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3777_ = lean_ctor_get(v_a_3773_, 0);
                v_start_3778_ = lean_ctor_get(v_a_3773_, 1);
                v_stop_3779_ = lean_ctor_get(v_a_3773_, 2);
                v_isSharedCheck_3873_ = (!lean_is_exclusive(v_a_3773_)) as u8;
                if v_isSharedCheck_3873_ == 0 {
                    v___x_3781_ = v_a_3773_;
                    v_isShared_3782_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_3779_);
                    lean_inc(v_start_3778_);
                    lean_inc(v_array_3777_);
                    lean_dec(v_a_3773_);
                    v___x_3781_ = lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3783_ = lean_nat_dec_lt(v_start_3778_, v_stop_3779_);
                if v___x_3783_ == 0 {
                    lean_del_object(v___x_3781_);
                    lean_dec(v_stop_3779_);
                    lean_dec(v_start_3778_);
                    lean_dec_ref(v_array_3777_);
                    v___x_3784_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3784_, 0, v_b_3774_);
                    lean_ctor_set(v___x_3784_, 1, v___y_3776_);
                    return v___x_3784_;
                } else {
                    v_fst_3785_ = lean_ctor_get(v_b_3774_, 0);
                    v_snd_3786_ = lean_ctor_get(v_b_3774_, 1);
                    v_isSharedCheck_3872_ = (!lean_is_exclusive(v_b_3774_)) as u8;
                    if v_isSharedCheck_3872_ == 0 {
                        v___x_3788_ = v_b_3774_;
                        v_isShared_3789_ = v_isSharedCheck_3872_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3786_);
                        lean_inc(v_fst_3785_);
                        lean_dec(v_b_3774_);
                        v___x_3788_ = lean_box(0);
                        v_isShared_3789_ = v_isSharedCheck_3872_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3790_ = lean_unsigned_to_nat(1);
                v___x_3791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0;
                v___x_3792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1;
                v___x_3793_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2;
                v___x_3794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                v___x_3795_ = lean_nat_add(v_start_3778_, v___x_3790_);
                lean_inc_ref(v_array_3777_);
                if v_isShared_3782_ == 0 {
                    lean_ctor_set(v___x_3781_, 1, v___x_3795_);
                    v___x_3797_ = v___x_3781_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_array_3777_);
                    lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3795_);
                    lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_stop_3779_);
                    v___x_3797_ = v_reuseFailAlloc_3871_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3823_ = lean_array_fget(v_array_3777_, v_start_3778_);
                lean_dec(v_start_3778_);
                lean_dec_ref(v_array_3777_);
                lean_inc(v___x_3823_);
                v___x_3824_ = l_Lean_Syntax_isOfKind(v___x_3823_, v___x_3794_);
                if v___x_3824_ == 0 {
                    lean_dec(v___x_3823_);
                    v___x_3825_ = l_Lean_Macro_throwUnsupported___redArg(v___y_3776_);
                    if lean_obj_tag(v___x_3825_) == 0 {
                        v_a_3826_ = lean_ctor_get(v___x_3825_, 1);
                        lean_inc(v_a_3826_);
                        lean_dec_ref_known(v___x_3825_, 2);
                        if v_isShared_3789_ == 0 {
                            v___x_3828_ = v___x_3788_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_fst_3785_);
                            lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_snd_3786_);
                            v___x_3828_ = v_reuseFailAlloc_3830_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3797_);
                        lean_del_object(v___x_3788_);
                        lean_dec(v_snd_3786_);
                        lean_dec(v_fst_3785_);
                        v_a_3831_ = lean_ctor_get(v___x_3825_, 0);
                        v_a_3832_ = lean_ctor_get(v___x_3825_, 1);
                        v_isSharedCheck_3839_ = (!lean_is_exclusive(v___x_3825_)) as u8;
                        if v_isSharedCheck_3839_ == 0 {
                            v___x_3834_ = v___x_3825_;
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3832_);
                            lean_inc(v_a_3831_);
                            lean_dec(v___x_3825_);
                            v___x_3834_ = lean_box(0);
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v___x_3840_ = lean_box((v___x_3772_) as usize);
                    v___f_3841_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                    lean_closure_set(v___f_3841_, 0, v___x_3840_);
                    v___x_3842_ = lean_unsigned_to_nat(3);
                    v___x_3843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5;
                    v___x_3844_ = lean_unsigned_to_nat(0);
                    v___x_3845_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3844_);
                    v___x_3846_ = l_Lean_Syntax_isNone(v___x_3845_);
                    if v___x_3846_ == 0 {
                        v___x_3847_ = lean_unsigned_to_nat(2);
                        lean_inc(v___x_3845_);
                        v___x_3848_ = l_Lean_Syntax_matchesNull(v___x_3845_, v___x_3847_);
                        if v___x_3848_ == 0 {
                            lean_dec(v___x_3845_);
                            lean_dec_ref(v___f_3841_);
                            lean_dec(v___x_3823_);
                            v___x_3849_ = l_Lean_Macro_throwUnsupported___redArg(v___y_3776_);
                            if lean_obj_tag(v___x_3849_) == 0 {
                                v_a_3850_ = lean_ctor_get(v___x_3849_, 1);
                                lean_inc(v_a_3850_);
                                lean_dec_ref_known(v___x_3849_, 2);
                                if v_isShared_3789_ == 0 {
                                    v___x_3852_ = v___x_3788_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_fst_3785_);
                                    lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_snd_3786_);
                                    v___x_3852_ = v_reuseFailAlloc_3854_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_3797_);
                                lean_del_object(v___x_3788_);
                                lean_dec(v_snd_3786_);
                                lean_dec(v_fst_3785_);
                                v_a_3855_ = lean_ctor_get(v___x_3849_, 0);
                                v_a_3856_ = lean_ctor_get(v___x_3849_, 1);
                                v_isSharedCheck_3863_ = (!lean_is_exclusive(v___x_3849_)) as u8;
                                if v_isSharedCheck_3863_ == 0 {
                                    v___x_3858_ = v___x_3849_;
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_3856_);
                                    lean_inc(v_a_3855_);
                                    lean_dec(v___x_3849_);
                                    v___x_3858_ = lean_box(0);
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_3788_);
                            v___x_3864_ = l_Lean_Syntax_getArg(v___x_3845_, v___x_3844_);
                            lean_dec(v___x_3845_);
                            v___x_3865_ = lean_box(0);
                            v___x_3866_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                            v___x_3867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_3823_, v___x_3790_, v___x_3842_, v___x_3772_, v___x_3791_, v___x_3792_, v___x_3793_, v___f_3841_, v_fst_3785_, v___x_3843_, v_snd_3786_, v___x_3865_, v___x_3866_, v___y_3775_, v___y_3776_);
                            lean_dec_ref_known(v___x_3866_, 1);
                            lean_dec(v___x_3823_);
                            v___y_3799_ = v___x_3867_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3845_);
                        lean_del_object(v___x_3788_);
                        v___x_3868_ = lean_box(0);
                        v___x_3869_ = lean_box(0);
                        v___x_3870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_3823_, v___x_3790_, v___x_3842_, v___x_3772_, v___x_3791_, v___x_3792_, v___x_3793_, v___f_3841_, v_fst_3785_, v___x_3843_, v_snd_3786_, v___x_3868_, v___x_3869_, v___y_3775_, v___y_3776_);
                        lean_dec(v___x_3823_);
                        v___y_3799_ = v___x_3870_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v___y_3799_) == 0 {
                    v_a_3800_ = lean_ctor_get(v___y_3799_, 0);
                    lean_inc(v_a_3800_);
                    if lean_obj_tag(v_a_3800_) == 0 {
                        lean_dec_ref(v___x_3797_);
                        v_a_3801_ = lean_ctor_get(v___y_3799_, 1);
                        v_isSharedCheck_3809_ = (!lean_is_exclusive(v___y_3799_)) as u8;
                        if v_isSharedCheck_3809_ == 0 {
                            v_unused_3810_ = lean_ctor_get(v___y_3799_, 0);
                            lean_dec(v_unused_3810_);
                            v___x_3803_ = v___y_3799_;
                            v_isShared_3804_ = v_isSharedCheck_3809_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3801_);
                            lean_dec(v___y_3799_);
                            v___x_3803_ = lean_box(0);
                            v_isShared_3804_ = v_isSharedCheck_3809_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_3811_ = lean_ctor_get(v___y_3799_, 1);
                        lean_inc(v_a_3811_);
                        lean_dec_ref_known(v___y_3799_, 2);
                        v_a_3812_ = lean_ctor_get(v_a_3800_, 0);
                        lean_inc(v_a_3812_);
                        lean_dec_ref_known(v_a_3800_, 1);
                        v_a_3773_ = v___x_3797_;
                        v_b_3774_ = v_a_3812_;
                        v___y_3776_ = v_a_3811_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3797_);
                    v_a_3814_ = lean_ctor_get(v___y_3799_, 0);
                    v_a_3815_ = lean_ctor_get(v___y_3799_, 1);
                    v_isSharedCheck_3822_ = (!lean_is_exclusive(v___y_3799_)) as u8;
                    if v_isSharedCheck_3822_ == 0 {
                        v___x_3817_ = v___y_3799_;
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3815_);
                        lean_inc(v_a_3814_);
                        lean_dec(v___y_3799_);
                        v___x_3817_ = lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_a_3805_ = lean_ctor_get(v_a_3800_, 0);
                lean_inc(v_a_3805_);
                lean_dec_ref_known(v_a_3800_, 1);
                if v_isShared_3804_ == 0 {
                    lean_ctor_set(v___x_3803_, 0, v_a_3805_);
                    v___x_3807_ = v___x_3803_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3805_);
                    lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_a_3801_);
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
                    v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3814_);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_a_3815_);
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
                    v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3831_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_a_3832_);
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
                    v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3855_);
                    lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3856_);
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
    mut v___x_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
    mut v_b_3876_: *mut LeanObject,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146766__boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut LeanObject = core::ptr::null_mut();
    v___x_146766__boxed_3879_ = (lean_unbox(v___x_3874_) as u8);
    v_res_3880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
        v___x_146766__boxed_3879_,
        v_a_3875_,
        v_b_3876_,
        v___y_3877_,
        v___y_3878_,
    );
    lean_dec_ref(v___y_3877_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_Elab_Do_expandDoFor(
    mut v_stx_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_ref_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4016_: u8 = 0;
    let mut v_a_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doElems_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_a_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4095_: u8 = 0;
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4173_: u8 = 0;
    let mut v_x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v_ref_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v___y_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: u8 = 0;
    let mut v___y_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doElems_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v___y_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v_decls_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    let mut v_decls_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_ref_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4374_: u8 = 0;
    let mut v_a_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doElems_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v_decls_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4486_: u8 = 0;
    let mut v_ref_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_a_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4511_: u8 = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doElems_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4581_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: u8 = 0;
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3940_ = l_Lean_Elab_Do_expandDoFor___closed__1;
                lean_inc(v_stx_3937_);
                v___x_3941_ = l_Lean_Syntax_isOfKind(v_stx_3937_, v___x_3940_);
                if v___x_3941_ == 0 {
                    lean_dec(v_stx_3937_);
                    v___x_3942_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                    return v___x_3942_;
                } else {
                    v___x_3943_ = lean_unsigned_to_nat(0);
                    v_tk_3944_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_3943_);
                    v___x_3945_ = lean_unsigned_to_nat(1);
                    v___x_3946_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_3945_);
                    lean_inc(v___x_3946_);
                    v___x_3947_ = l_Lean_Syntax_matchesNull(v___x_3946_, v___x_3945_);
                    if v___x_3947_ == 0 {
                        v___x_3948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        v_decls_3980_ = l_Lean_Syntax_getArgs(v___x_3946_);
                        lean_dec(v___x_3946_);
                        v_decls_3981_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_3980_);
                        lean_dec_ref(v_decls_3980_);
                        v___x_4026_ = lean_box(0);
                        v___x_4027_ = lean_array_get(v___x_4026_, v_decls_3981_, v___x_3943_);
                        lean_inc(v___x_4027_);
                        v___x_4028_ = l_Lean_Syntax_isOfKind(v___x_4027_, v___x_3948_);
                        if v___x_4028_ == 0 {
                            lean_dec(v___x_4027_);
                            lean_dec_ref(v_decls_3981_);
                            lean_dec(v_tk_3944_);
                            lean_dec(v_stx_3937_);
                            v___x_4029_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                            return v___x_4029_;
                        } else {
                            v___x_4030_ = lean_unsigned_to_nat(3);
                            v_body_4031_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4030_);
                            lean_dec(v_stx_3937_);
                            v___x_4096_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_3943_);
                            v___x_4097_ = l_Lean_Syntax_isNone(v___x_4096_);
                            if v___x_4097_ == 0 {
                                v___x_4098_ = lean_unsigned_to_nat(2);
                                lean_inc(v___x_4096_);
                                v___x_4099_ = l_Lean_Syntax_matchesNull(v___x_4096_, v___x_4098_);
                                if v___x_4099_ == 0 {
                                    lean_dec(v___x_4096_);
                                    lean_dec(v_body_4031_);
                                    lean_dec(v___x_4027_);
                                    lean_dec_ref(v_decls_3981_);
                                    lean_dec(v_tk_3944_);
                                    v___x_4100_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                    return v___x_4100_;
                                } else {
                                    v_h_x3f_4101_ = l_Lean_Syntax_getArg(v___x_4096_, v___x_3943_);
                                    lean_dec(v___x_4096_);
                                    v___x_4102_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_4102_, 0, v_h_x3f_4101_);
                                    v_h_x3f_4033_ = v___x_4102_;
                                    v___y_4034_ = v_a_3938_;
                                    v___y_4035_ = v_a_3939_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4096_);
                                v___x_4103_ = lean_box(0);
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
                        lean_inc(v___x_4104_);
                        v___x_4337_ = l_Lean_Syntax_isOfKind(v___x_4104_, v___x_4105_);
                        if v___x_4337_ == 0 {
                            lean_dec(v___x_4104_);
                            v_decls_4338_ = l_Lean_Syntax_getArgs(v___x_3946_);
                            lean_dec(v___x_3946_);
                            v_decls_4339_ =
                                l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4338_);
                            lean_dec_ref(v_decls_4338_);
                            v___x_4384_ = lean_box(0);
                            v___x_4385_ = lean_array_get(v___x_4384_, v_decls_4339_, v___x_3943_);
                            lean_inc(v___x_4385_);
                            v___x_4386_ = l_Lean_Syntax_isOfKind(v___x_4385_, v___x_4105_);
                            if v___x_4386_ == 0 {
                                lean_dec(v___x_4385_);
                                lean_dec_ref(v_decls_4339_);
                                lean_dec(v_tk_3944_);
                                lean_dec(v_stx_3937_);
                                v___x_4387_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                return v___x_4387_;
                            } else {
                                v___x_4388_ = lean_unsigned_to_nat(3);
                                v_body_4389_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4388_);
                                lean_dec(v_stx_3937_);
                                v___x_4454_ = l_Lean_Syntax_getArg(v___x_4385_, v___x_3943_);
                                v___x_4455_ = l_Lean_Syntax_isNone(v___x_4454_);
                                if v___x_4455_ == 0 {
                                    v___x_4456_ = lean_unsigned_to_nat(2);
                                    lean_inc(v___x_4454_);
                                    v___x_4457_ =
                                        l_Lean_Syntax_matchesNull(v___x_4454_, v___x_4456_);
                                    if v___x_4457_ == 0 {
                                        lean_dec(v___x_4454_);
                                        lean_dec(v_body_4389_);
                                        lean_dec(v___x_4385_);
                                        lean_dec_ref(v_decls_4339_);
                                        lean_dec(v_tk_3944_);
                                        v___x_4458_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                        return v___x_4458_;
                                    } else {
                                        v_h_x3f_4459_ =
                                            l_Lean_Syntax_getArg(v___x_4454_, v___x_3943_);
                                        lean_dec(v___x_4454_);
                                        v___x_4460_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v___x_4460_, 0, v_h_x3f_4459_);
                                        v_h_x3f_4391_ = v___x_4460_;
                                        v___y_4392_ = v_a_3938_;
                                        v___y_4393_ = v_a_3939_;
                                        state = 31;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_4454_);
                                    v___x_4461_ = lean_box(0);
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
                                v___x_4464_ = lean_unsigned_to_nat(2);
                                v___x_4465_ = l_Lean_Syntax_matchesNull(v___x_4462_, v___x_4464_);
                                if v___x_4465_ == 0 {
                                    lean_dec(v___x_4104_);
                                    v_decls_4466_ = l_Lean_Syntax_getArgs(v___x_3946_);
                                    lean_dec(v___x_3946_);
                                    v_decls_4467_ =
                                        l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4466_);
                                    lean_dec_ref(v_decls_4466_);
                                    v___x_4512_ = lean_box(0);
                                    v___x_4513_ =
                                        lean_array_get(v___x_4512_, v_decls_4467_, v___x_3943_);
                                    lean_inc(v___x_4513_);
                                    v___x_4514_ = l_Lean_Syntax_isOfKind(v___x_4513_, v___x_4105_);
                                    if v___x_4514_ == 0 {
                                        lean_dec(v___x_4513_);
                                        lean_dec_ref(v_decls_4467_);
                                        lean_dec(v_tk_3944_);
                                        lean_dec(v_stx_3937_);
                                        v___x_4515_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                        return v___x_4515_;
                                    } else {
                                        v___x_4516_ = lean_unsigned_to_nat(3);
                                        v_body_4517_ =
                                            l_Lean_Syntax_getArg(v_stx_3937_, v___x_4516_);
                                        lean_dec(v_stx_3937_);
                                        v___x_4582_ =
                                            l_Lean_Syntax_getArg(v___x_4513_, v___x_3943_);
                                        v___x_4583_ = l_Lean_Syntax_isNone(v___x_4582_);
                                        if v___x_4583_ == 0 {
                                            lean_inc(v___x_4582_);
                                            v___x_4584_ =
                                                l_Lean_Syntax_matchesNull(v___x_4582_, v___x_4464_);
                                            if v___x_4584_ == 0 {
                                                lean_dec(v___x_4582_);
                                                lean_dec(v_body_4517_);
                                                lean_dec(v___x_4513_);
                                                lean_dec_ref(v_decls_4467_);
                                                lean_dec(v_tk_3944_);
                                                v___x_4585_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v_a_3939_,
                                                    );
                                                return v___x_4585_;
                                            } else {
                                                v_h_x3f_4586_ =
                                                    l_Lean_Syntax_getArg(v___x_4582_, v___x_3943_);
                                                lean_dec(v___x_4582_);
                                                v___x_4587_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_4587_, 0, v_h_x3f_4586_);
                                                v_h_x3f_4519_ = v___x_4587_;
                                                v___y_4520_ = v_a_3938_;
                                                v___y_4521_ = v_a_3939_;
                                                state = 41;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_4582_);
                                            v___x_4588_ = lean_box(0);
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
                                lean_dec(v___x_4462_);
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
                lean_inc_ref_n(v___y_3953_, 3);
                v___x_3961_ = l_Array_append___redArg(v___y_3953_, v___y_3960_);
                lean_dec_ref(v___y_3960_);
                lean_inc_n(v___y_3959_, 4);
                lean_inc_n(v___y_3952_, 10);
                v___x_3962_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3962_, 0, v___y_3952_);
                lean_ctor_set(v___x_3962_, 1, v___y_3959_);
                lean_ctor_set(v___x_3962_, 2, v___x_3961_);
                v___x_3963_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_3964_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3964_, 0, v___y_3952_);
                lean_ctor_set(v___x_3964_, 1, v___x_3963_);
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
                v___x_3968_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3968_, 0, v___y_3952_);
                lean_ctor_set(v___x_3968_, 1, v___x_3967_);
                lean_inc_ref(v___x_3968_);
                v___x_3969_ = l_Lean_Syntax_node4(
                    v___y_3952_,
                    v___x_3940_,
                    v___y_3958_,
                    v___x_3966_,
                    v___x_3968_,
                    v___y_3950_,
                );
                v___x_3970_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3970_, 0, v___y_3952_);
                lean_ctor_set(v___x_3970_, 1, v___y_3959_);
                lean_ctor_set(v___x_3970_, 2, v___y_3953_);
                lean_inc(v___y_3957_);
                v___x_3971_ =
                    l_Lean_Syntax_node2(v___y_3952_, v___y_3957_, v___x_3969_, v___x_3970_);
                v___x_3972_ = lean_array_push(v___y_3956_, v___x_3971_);
                v___x_3973_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_3974_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_3975_ = l_Array_append___redArg(v___y_3953_, v___x_3972_);
                lean_dec_ref(v___x_3972_);
                v___x_3976_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3976_, 0, v___y_3952_);
                lean_ctor_set(v___x_3976_, 1, v___y_3959_);
                lean_ctor_set(v___x_3976_, 2, v___x_3975_);
                v___x_3977_ = l_Lean_Syntax_node1(v___y_3952_, v___x_3974_, v___x_3976_);
                v___x_3978_ =
                    l_Lean_Syntax_node2(v___y_3952_, v___x_3973_, v___x_3968_, v___x_3977_);
                v___x_3979_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3979_, 0, v___x_3978_);
                lean_ctor_set(v___x_3979_, 1, v___y_3955_);
                return v___x_3979_;
            }
            2 => {
                v___x_3990_ = lean_array_get_size(v_decls_3981_);
                v___x_3991_ = l_Array_toSubarray___redArg(v_decls_3981_, v___x_3945_, v___x_3990_);
                lean_inc_ref(v___y_3983_);
                v___x_3992_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3992_, 0, v___y_3983_);
                lean_ctor_set(v___x_3992_, 1, v_body_3987_);
                v___x_3993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_3947_, v___x_3991_, v___x_3992_, v___y_3988_, v___y_3989_);
                if lean_obj_tag(v___x_3993_) == 0 {
                    v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
                    lean_inc(v_a_3994_);
                    v_a_3995_ = lean_ctor_get(v___x_3993_, 1);
                    lean_inc(v_a_3995_);
                    lean_dec_ref_known(v___x_3993_, 2);
                    v_fst_3996_ = lean_ctor_get(v_a_3994_, 0);
                    v_snd_3997_ = lean_ctor_get(v_a_3994_, 1);
                    v_isSharedCheck_4016_ = (!lean_is_exclusive(v_a_3994_)) as u8;
                    if v_isSharedCheck_4016_ == 0 {
                        v___x_3999_ = v_a_3994_;
                        v_isShared_4000_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_3997_);
                        lean_inc(v_fst_3996_);
                        lean_dec(v_a_3994_);
                        v___x_3999_ = lean_box(0);
                        v_isShared_4000_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3986_);
                    lean_dec(v___y_3985_);
                    lean_dec(v___y_3984_);
                    lean_dec(v_tk_3944_);
                    v_a_4017_ = lean_ctor_get(v___x_3993_, 0);
                    v_a_4018_ = lean_ctor_get(v___x_3993_, 1);
                    v_isSharedCheck_4025_ = (!lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4025_ == 0 {
                        v___x_4020_ = v___x_3993_;
                        v_isShared_4021_ = v_isSharedCheck_4025_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4018_);
                        lean_inc(v_a_4017_);
                        lean_dec(v___x_3993_);
                        v___x_4020_ = lean_box(0);
                        v_isShared_4021_ = v_isSharedCheck_4025_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_4001_ = lean_ctor_get(v___y_3988_, 5);
                v___x_4002_ = l_Lean_SourceInfo_fromRef(v_ref_4001_, v___x_3947_);
                v___x_4003_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4004_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                lean_dec(v_tk_3944_);
                v___x_4005_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4000_ == 0 {
                    lean_ctor_set_tag(v___x_3999_, 2);
                    lean_ctor_set(v___x_3999_, 1, v___x_4005_);
                    lean_ctor_set(v___x_3999_, 0, v___x_4004_);
                    v___x_4007_ = v___x_3999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4015_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4004_);
                    lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4009_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if lean_obj_tag(v___y_3985_) == 1 {
                    v_val_4010_ = lean_ctor_get(v___y_3985_, 0);
                    lean_inc(v_val_4010_);
                    lean_dec_ref_known(v___y_3985_, 1);
                    v___x_4011_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    lean_inc(v___x_4002_);
                    v___x_4012_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4012_, 0, v___x_4002_);
                    lean_ctor_set(v___x_4012_, 1, v___x_4011_);
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
                    lean_dec(v___y_3985_);
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
                    v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4017_);
                    lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_a_4018_);
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
                lean_dec(v___x_4027_);
                v_doElems_4038_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4039_ = l_Lean_Syntax_isIdent(v___x_4036_);
                if v___x_4039_ == 0 {
                    v___x_4040_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    lean_inc(v___x_4036_);
                    v___x_4041_ = l_Lean_Syntax_isOfKind(v___x_4036_, v___x_4040_);
                    if v___x_4041_ == 0 {
                        v___x_4042_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4036_,
                                v___x_4041_,
                                v___y_4034_,
                                v___y_4035_,
                            );
                        if lean_obj_tag(v___x_4042_) == 0 {
                            v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
                            lean_inc_n(v_a_4043_, 2);
                            v_a_4044_ = lean_ctor_get(v___x_4042_, 1);
                            lean_inc(v_a_4044_);
                            lean_dec_ref_known(v___x_4042_, 2);
                            v_ref_4045_ = lean_ctor_get(v___y_4034_, 5);
                            v___x_4046_ = l_Lean_SourceInfo_fromRef(v_ref_4045_, v___x_4041_);
                            v___x_4047_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4049_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4050_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            lean_inc_n(v___x_4046_, 15);
                            v___x_4052_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4052_, 0, v___x_4046_);
                            lean_ctor_set(v___x_4052_, 1, v___x_4051_);
                            v___x_4053_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4054_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_4054_, 0, v___x_4046_);
                            lean_ctor_set(v___x_4054_, 1, v___x_4048_);
                            lean_ctor_set(v___x_4054_, 2, v___x_4053_);
                            v___x_4055_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            lean_inc_ref_n(v___x_4054_, 4);
                            v___x_4056_ = l_Lean_Syntax_node2(
                                v___x_4046_,
                                v___x_4055_,
                                v___x_4054_,
                                v_a_4043_,
                            );
                            v___x_4057_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4056_);
                            v___x_4058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4059_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4059_, 0, v___x_4046_);
                            lean_ctor_set(v___x_4059_, 1, v___x_4058_);
                            v___x_4060_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4061_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4063_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4063_, 0, v___x_4046_);
                            lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                            v___x_4064_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4036_);
                            v___x_4065_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4064_);
                            v___x_4066_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4067_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4067_, 0, v___x_4046_);
                            lean_ctor_set(v___x_4067_, 1, v___x_4066_);
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
                            lean_dec(v___x_4037_);
                            lean_dec(v___x_4036_);
                            lean_dec(v_h_x3f_4033_);
                            lean_dec(v_body_4031_);
                            lean_dec_ref(v_decls_3981_);
                            lean_dec(v_tk_3944_);
                            v_a_4075_ = lean_ctor_get(v___x_4042_, 0);
                            v_a_4076_ = lean_ctor_get(v___x_4042_, 1);
                            v_isSharedCheck_4083_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4083_ == 0 {
                                v___x_4078_ = v___x_4042_;
                                v_isShared_4079_ = v_isSharedCheck_4083_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4076_);
                                lean_inc(v_a_4075_);
                                lean_dec(v___x_4042_);
                                v___x_4078_ = lean_box(0);
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
                        lean_dec(v___x_4036_);
                        if lean_obj_tag(v___x_4084_) == 0 {
                            v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
                            lean_inc(v_a_4085_);
                            v_a_4086_ = lean_ctor_get(v___x_4084_, 1);
                            lean_inc(v_a_4086_);
                            lean_dec_ref_known(v___x_4084_, 2);
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
                            lean_dec(v___x_4037_);
                            lean_dec(v_h_x3f_4033_);
                            lean_dec(v_body_4031_);
                            lean_dec_ref(v_decls_3981_);
                            lean_dec(v_tk_3944_);
                            v_a_4087_ = lean_ctor_get(v___x_4084_, 0);
                            v_a_4088_ = lean_ctor_get(v___x_4084_, 1);
                            v_isSharedCheck_4095_ = (!lean_is_exclusive(v___x_4084_)) as u8;
                            if v_isSharedCheck_4095_ == 0 {
                                v___x_4090_ = v___x_4084_;
                                v_isShared_4091_ = v_isSharedCheck_4095_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_4088_);
                                lean_inc(v_a_4087_);
                                lean_dec(v___x_4084_);
                                v___x_4090_ = lean_box(0);
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
                    v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4075_);
                    lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_a_4076_);
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
                    v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4087_);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_a_4088_);
                    v___x_4093_ = v_reuseFailAlloc_4094_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4093_;
            }
            12 => {
                lean_inc_ref_n(v___y_4115_, 3);
                v___x_4118_ = l_Array_append___redArg(v___y_4115_, v___y_4117_);
                lean_dec_ref(v___y_4117_);
                lean_inc_n(v___y_4110_, 4);
                lean_inc_n(v___y_4108_, 10);
                v___x_4119_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4119_, 0, v___y_4108_);
                lean_ctor_set(v___x_4119_, 1, v___y_4110_);
                lean_ctor_set(v___x_4119_, 2, v___x_4118_);
                v___x_4120_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4121_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4121_, 0, v___y_4108_);
                lean_ctor_set(v___x_4121_, 1, v___x_4120_);
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
                v___x_4125_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4125_, 0, v___y_4108_);
                lean_ctor_set(v___x_4125_, 1, v___x_4124_);
                lean_inc_ref(v___x_4125_);
                v___x_4126_ = l_Lean_Syntax_node4(
                    v___y_4108_,
                    v___x_3940_,
                    v___y_4116_,
                    v___x_4123_,
                    v___x_4125_,
                    v___y_4112_,
                );
                v___x_4127_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4127_, 0, v___y_4108_);
                lean_ctor_set(v___x_4127_, 1, v___y_4110_);
                lean_ctor_set(v___x_4127_, 2, v___y_4115_);
                lean_inc(v___y_4113_);
                v___x_4128_ =
                    l_Lean_Syntax_node2(v___y_4108_, v___y_4113_, v___x_4126_, v___x_4127_);
                v___x_4129_ = lean_array_push(v___y_4111_, v___x_4128_);
                v___x_4130_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4131_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4132_ = l_Array_append___redArg(v___y_4115_, v___x_4129_);
                lean_dec_ref(v___x_4129_);
                v___x_4133_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4133_, 0, v___y_4108_);
                lean_ctor_set(v___x_4133_, 1, v___y_4110_);
                lean_ctor_set(v___x_4133_, 2, v___x_4132_);
                v___x_4134_ = l_Lean_Syntax_node1(v___y_4108_, v___x_4131_, v___x_4133_);
                v___x_4135_ =
                    l_Lean_Syntax_node2(v___y_4108_, v___x_4130_, v___x_4125_, v___x_4134_);
                v___x_4136_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                lean_ctor_set(v___x_4136_, 1, v___y_4109_);
                return v___x_4136_;
            }
            13 => {
                lean_inc_ref_n(v___y_4144_, 3);
                v___x_4149_ = l_Array_append___redArg(v___y_4144_, v___y_4148_);
                lean_dec_ref(v___y_4148_);
                lean_inc_n(v___y_4141_, 4);
                lean_inc_n(v___y_4145_, 10);
                v___x_4150_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4150_, 0, v___y_4145_);
                lean_ctor_set(v___x_4150_, 1, v___y_4141_);
                lean_ctor_set(v___x_4150_, 2, v___x_4149_);
                v___x_4151_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4152_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4152_, 0, v___y_4145_);
                lean_ctor_set(v___x_4152_, 1, v___x_4151_);
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
                v___x_4156_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4156_, 0, v___y_4145_);
                lean_ctor_set(v___x_4156_, 1, v___x_4155_);
                lean_inc_ref(v___x_4156_);
                v___x_4157_ = l_Lean_Syntax_node4(
                    v___y_4145_,
                    v___x_3940_,
                    v___y_4143_,
                    v___x_4154_,
                    v___x_4156_,
                    v___y_4138_,
                );
                v___x_4158_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4158_, 0, v___y_4145_);
                lean_ctor_set(v___x_4158_, 1, v___y_4141_);
                lean_ctor_set(v___x_4158_, 2, v___y_4144_);
                lean_inc(v___y_4142_);
                v___x_4159_ =
                    l_Lean_Syntax_node2(v___y_4145_, v___y_4142_, v___x_4157_, v___x_4158_);
                v___x_4160_ = lean_array_push(v___y_4146_, v___x_4159_);
                v___x_4161_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4162_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4163_ = l_Array_append___redArg(v___y_4144_, v___x_4160_);
                lean_dec_ref(v___x_4160_);
                v___x_4164_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4164_, 0, v___y_4145_);
                lean_ctor_set(v___x_4164_, 1, v___y_4141_);
                lean_ctor_set(v___x_4164_, 2, v___x_4163_);
                v___x_4165_ = l_Lean_Syntax_node1(v___y_4145_, v___x_4162_, v___x_4164_);
                v___x_4166_ =
                    l_Lean_Syntax_node2(v___y_4145_, v___x_4161_, v___x_4156_, v___x_4165_);
                v___x_4167_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4167_, 0, v___x_4166_);
                lean_ctor_set(v___x_4167_, 1, v___y_4147_);
                return v___x_4167_;
            }
            14 => {
                v___x_4178_ = lean_array_get_size(v___y_4171_);
                v___x_4179_ = l_Array_toSubarray___redArg(v___y_4171_, v___x_3945_, v___x_4178_);
                lean_inc_ref(v___y_4172_);
                v___x_4180_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4180_, 0, v___y_4172_);
                lean_ctor_set(v___x_4180_, 1, v_body_4175_);
                v___x_4181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_4173_, v___x_4179_, v___x_4180_, v___y_4176_, v___y_4177_);
                if lean_obj_tag(v___x_4181_) == 0 {
                    v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
                    lean_inc(v_a_4182_);
                    v_a_4183_ = lean_ctor_get(v___x_4181_, 1);
                    lean_inc(v_a_4183_);
                    lean_dec_ref_known(v___x_4181_, 2);
                    v_fst_4184_ = lean_ctor_get(v_a_4182_, 0);
                    v_snd_4185_ = lean_ctor_get(v_a_4182_, 1);
                    v_isSharedCheck_4204_ = (!lean_is_exclusive(v_a_4182_)) as u8;
                    if v_isSharedCheck_4204_ == 0 {
                        v___x_4187_ = v_a_4182_;
                        v_isShared_4188_ = v_isSharedCheck_4204_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_snd_4185_);
                        lean_inc(v_fst_4184_);
                        lean_dec(v_a_4182_);
                        v___x_4187_ = lean_box(0);
                        v_isShared_4188_ = v_isSharedCheck_4204_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_dec(v_x_4174_);
                    lean_dec(v___y_4170_);
                    lean_dec(v___y_4169_);
                    lean_dec(v_tk_3944_);
                    v_a_4205_ = lean_ctor_get(v___x_4181_, 0);
                    v_a_4206_ = lean_ctor_get(v___x_4181_, 1);
                    v_isSharedCheck_4213_ = (!lean_is_exclusive(v___x_4181_)) as u8;
                    if v_isSharedCheck_4213_ == 0 {
                        v___x_4208_ = v___x_4181_;
                        v_isShared_4209_ = v_isSharedCheck_4213_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4206_);
                        lean_inc(v_a_4205_);
                        lean_dec(v___x_4181_);
                        v___x_4208_ = lean_box(0);
                        v_isShared_4209_ = v_isSharedCheck_4213_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                v_ref_4189_ = lean_ctor_get(v___y_4176_, 5);
                v___x_4190_ = l_Lean_SourceInfo_fromRef(v_ref_4189_, v___y_4173_);
                v___x_4191_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4192_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                lean_dec(v_tk_3944_);
                v___x_4193_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4188_ == 0 {
                    lean_ctor_set_tag(v___x_4187_, 2);
                    lean_ctor_set(v___x_4187_, 1, v___x_4193_);
                    lean_ctor_set(v___x_4187_, 0, v___x_4192_);
                    v___x_4195_ = v___x_4187_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4192_);
                    lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___x_4193_);
                    v___x_4195_ = v_reuseFailAlloc_4203_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4197_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if lean_obj_tag(v___y_4170_) == 1 {
                    v_val_4198_ = lean_ctor_get(v___y_4170_, 0);
                    lean_inc(v_val_4198_);
                    lean_dec_ref_known(v___y_4170_, 1);
                    v___x_4199_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    lean_inc(v___x_4190_);
                    v___x_4200_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4200_, 0, v___x_4190_);
                    lean_ctor_set(v___x_4200_, 1, v___x_4199_);
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
                    lean_dec(v___y_4170_);
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
                    v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4205_);
                    lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_a_4206_);
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
                lean_dec(v___y_4219_);
                v_doElems_4225_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4226_ = l_Lean_Syntax_isIdent(v___x_4223_);
                if v___x_4226_ == 0 {
                    v___x_4227_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    lean_inc(v___x_4223_);
                    v___x_4228_ = l_Lean_Syntax_isOfKind(v___x_4223_, v___x_4227_);
                    if v___x_4228_ == 0 {
                        v___x_4229_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4223_,
                                v___y_4218_,
                                v___y_4221_,
                                v___y_4222_,
                            );
                        if lean_obj_tag(v___x_4229_) == 0 {
                            v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
                            lean_inc_n(v_a_4230_, 2);
                            v_a_4231_ = lean_ctor_get(v___x_4229_, 1);
                            lean_inc(v_a_4231_);
                            lean_dec_ref_known(v___x_4229_, 2);
                            v_ref_4232_ = lean_ctor_get(v___y_4221_, 5);
                            v___x_4233_ = l_Lean_SourceInfo_fromRef(v_ref_4232_, v___y_4218_);
                            v___x_4234_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4236_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4237_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            lean_inc_n(v___x_4233_, 15);
                            v___x_4239_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4239_, 0, v___x_4233_);
                            lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                            v___x_4240_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4241_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_4241_, 0, v___x_4233_);
                            lean_ctor_set(v___x_4241_, 1, v___x_4235_);
                            lean_ctor_set(v___x_4241_, 2, v___x_4240_);
                            v___x_4242_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            lean_inc_ref_n(v___x_4241_, 4);
                            v___x_4243_ = l_Lean_Syntax_node2(
                                v___x_4233_,
                                v___x_4242_,
                                v___x_4241_,
                                v_a_4230_,
                            );
                            v___x_4244_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4243_);
                            v___x_4245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4246_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4246_, 0, v___x_4233_);
                            lean_ctor_set(v___x_4246_, 1, v___x_4245_);
                            v___x_4247_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4248_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4250_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4250_, 0, v___x_4233_);
                            lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                            v___x_4251_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4223_);
                            v___x_4252_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4251_);
                            v___x_4253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4254_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4254_, 0, v___x_4233_);
                            lean_ctor_set(v___x_4254_, 1, v___x_4253_);
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
                            lean_dec(v___x_4224_);
                            lean_dec(v___x_4223_);
                            lean_dec(v_h_x3f_4220_);
                            lean_dec(v___y_4217_);
                            lean_dec_ref(v___y_4216_);
                            lean_dec(v_tk_3944_);
                            v_a_4262_ = lean_ctor_get(v___x_4229_, 0);
                            v_a_4263_ = lean_ctor_get(v___x_4229_, 1);
                            v_isSharedCheck_4270_ = (!lean_is_exclusive(v___x_4229_)) as u8;
                            if v_isSharedCheck_4270_ == 0 {
                                v___x_4265_ = v___x_4229_;
                                v_isShared_4266_ = v_isSharedCheck_4270_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_4263_);
                                lean_inc(v_a_4262_);
                                lean_dec(v___x_4229_);
                                v___x_4265_ = lean_box(0);
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
                        lean_dec(v___x_4223_);
                        if lean_obj_tag(v___x_4271_) == 0 {
                            v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
                            lean_inc(v_a_4272_);
                            v_a_4273_ = lean_ctor_get(v___x_4271_, 1);
                            lean_inc(v_a_4273_);
                            lean_dec_ref_known(v___x_4271_, 2);
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
                            lean_dec(v___x_4224_);
                            lean_dec(v_h_x3f_4220_);
                            lean_dec(v___y_4217_);
                            lean_dec_ref(v___y_4216_);
                            lean_dec(v_tk_3944_);
                            v_a_4274_ = lean_ctor_get(v___x_4271_, 0);
                            v_a_4275_ = lean_ctor_get(v___x_4271_, 1);
                            v_isSharedCheck_4282_ = (!lean_is_exclusive(v___x_4271_)) as u8;
                            if v_isSharedCheck_4282_ == 0 {
                                v___x_4277_ = v___x_4271_;
                                v_isShared_4278_ = v_isSharedCheck_4282_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_4275_);
                                lean_inc(v_a_4274_);
                                lean_dec(v___x_4271_);
                                v___x_4277_ = lean_box(0);
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
                    v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4262_);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_a_4263_);
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
                    v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4274_);
                    lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_a_4275_);
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
                lean_dec(v___x_4104_);
                v___x_4287_ = l_Lean_Elab_Do_expandDoFor___closed__16;
                v___x_4288_ = l_Lean_Syntax_isOfKind(v___x_4286_, v___x_4287_);
                if v___x_4288_ == 0 {
                    v_decls_4289_ = l_Lean_Syntax_getArgs(v___x_3946_);
                    lean_dec(v___x_3946_);
                    v_decls_4290_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4289_);
                    lean_dec_ref(v_decls_4289_);
                    v___x_4291_ = lean_box(0);
                    v___x_4292_ = lean_array_get(v___x_4291_, v_decls_4290_, v___x_3943_);
                    lean_inc(v___x_4292_);
                    v___x_4293_ = l_Lean_Syntax_isOfKind(v___x_4292_, v___x_4105_);
                    if v___x_4293_ == 0 {
                        lean_dec(v___x_4292_);
                        lean_dec_ref(v_decls_4290_);
                        lean_dec(v_tk_3944_);
                        lean_dec(v_stx_3937_);
                        v___x_4294_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                        return v___x_4294_;
                    } else {
                        v___x_4295_ = lean_unsigned_to_nat(3);
                        v_body_4296_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4295_);
                        lean_dec(v_stx_3937_);
                        v___x_4297_ = l_Lean_Syntax_getArg(v___x_4292_, v___x_3943_);
                        v___x_4298_ = l_Lean_Syntax_isNone(v___x_4297_);
                        if v___x_4298_ == 0 {
                            v___x_4299_ = lean_unsigned_to_nat(2);
                            lean_inc(v___x_4297_);
                            v___x_4300_ = l_Lean_Syntax_matchesNull(v___x_4297_, v___x_4299_);
                            if v___x_4300_ == 0 {
                                lean_dec(v___x_4297_);
                                lean_dec(v_body_4296_);
                                lean_dec(v___x_4292_);
                                lean_dec_ref(v_decls_4290_);
                                lean_dec(v_tk_3944_);
                                v___x_4301_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                                return v___x_4301_;
                            } else {
                                v_h_x3f_4302_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_3943_);
                                lean_dec(v___x_4297_);
                                v___x_4303_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4303_, 0, v_h_x3f_4302_);
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
                            lean_dec(v___x_4297_);
                            v___x_4304_ = lean_box(0);
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
                    lean_dec(v___x_3946_);
                    lean_dec(v_tk_3944_);
                    lean_dec(v_stx_3937_);
                    v___x_4305_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                    return v___x_4305_;
                }
            }
            25 => {
                lean_inc_ref_n(v___y_4311_, 3);
                v___x_4318_ = l_Array_append___redArg(v___y_4311_, v___y_4317_);
                lean_dec_ref(v___y_4317_);
                lean_inc_n(v___y_4307_, 4);
                lean_inc_n(v___y_4308_, 10);
                v___x_4319_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4319_, 0, v___y_4308_);
                lean_ctor_set(v___x_4319_, 1, v___y_4307_);
                lean_ctor_set(v___x_4319_, 2, v___x_4318_);
                v___x_4320_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4321_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4321_, 0, v___y_4308_);
                lean_ctor_set(v___x_4321_, 1, v___x_4320_);
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
                v___x_4325_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4325_, 0, v___y_4308_);
                lean_ctor_set(v___x_4325_, 1, v___x_4324_);
                lean_inc_ref(v___x_4325_);
                v___x_4326_ = l_Lean_Syntax_node4(
                    v___y_4308_,
                    v___x_3940_,
                    v___y_4312_,
                    v___x_4323_,
                    v___x_4325_,
                    v___y_4310_,
                );
                v___x_4327_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4327_, 0, v___y_4308_);
                lean_ctor_set(v___x_4327_, 1, v___y_4307_);
                lean_ctor_set(v___x_4327_, 2, v___y_4311_);
                lean_inc(v___y_4313_);
                v___x_4328_ =
                    l_Lean_Syntax_node2(v___y_4308_, v___y_4313_, v___x_4326_, v___x_4327_);
                v___x_4329_ = lean_array_push(v___y_4309_, v___x_4328_);
                v___x_4330_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4331_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4332_ = l_Array_append___redArg(v___y_4311_, v___x_4329_);
                lean_dec_ref(v___x_4329_);
                v___x_4333_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4333_, 0, v___y_4308_);
                lean_ctor_set(v___x_4333_, 1, v___y_4307_);
                lean_ctor_set(v___x_4333_, 2, v___x_4332_);
                v___x_4334_ = l_Lean_Syntax_node1(v___y_4308_, v___x_4331_, v___x_4333_);
                v___x_4335_ =
                    l_Lean_Syntax_node2(v___y_4308_, v___x_4330_, v___x_4325_, v___x_4334_);
                v___x_4336_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4336_, 0, v___x_4335_);
                lean_ctor_set(v___x_4336_, 1, v___y_4316_);
                return v___x_4336_;
            }
            26 => {
                v___x_4348_ = lean_array_get_size(v_decls_4339_);
                v___x_4349_ = l_Array_toSubarray___redArg(v_decls_4339_, v___x_3945_, v___x_4348_);
                lean_inc_ref(v___y_4343_);
                v___x_4350_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4350_, 0, v___y_4343_);
                lean_ctor_set(v___x_4350_, 1, v_body_4345_);
                v___x_4351_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_4337_, v___x_4349_, v___x_4350_, v___y_4346_, v___y_4347_);
                if lean_obj_tag(v___x_4351_) == 0 {
                    v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
                    lean_inc(v_a_4352_);
                    v_a_4353_ = lean_ctor_get(v___x_4351_, 1);
                    lean_inc(v_a_4353_);
                    lean_dec_ref_known(v___x_4351_, 2);
                    v_fst_4354_ = lean_ctor_get(v_a_4352_, 0);
                    v_snd_4355_ = lean_ctor_get(v_a_4352_, 1);
                    v_isSharedCheck_4374_ = (!lean_is_exclusive(v_a_4352_)) as u8;
                    if v_isSharedCheck_4374_ == 0 {
                        v___x_4357_ = v_a_4352_;
                        v_isShared_4358_ = v_isSharedCheck_4374_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_snd_4355_);
                        lean_inc(v_fst_4354_);
                        lean_dec(v_a_4352_);
                        v___x_4357_ = lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4374_;
                        state = 27;
                        continue;
                    }
                } else {
                    lean_dec(v_x_4344_);
                    lean_dec(v___y_4342_);
                    lean_dec(v___y_4341_);
                    lean_dec(v_tk_3944_);
                    v_a_4375_ = lean_ctor_get(v___x_4351_, 0);
                    v_a_4376_ = lean_ctor_get(v___x_4351_, 1);
                    v_isSharedCheck_4383_ = (!lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4378_ = v___x_4351_;
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_4376_);
                        lean_inc(v_a_4375_);
                        lean_dec(v___x_4351_);
                        v___x_4378_ = lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                v_ref_4359_ = lean_ctor_get(v___y_4346_, 5);
                v___x_4360_ = l_Lean_SourceInfo_fromRef(v_ref_4359_, v___x_4337_);
                v___x_4361_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4362_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                lean_dec(v_tk_3944_);
                v___x_4363_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4358_ == 0 {
                    lean_ctor_set_tag(v___x_4357_, 2);
                    lean_ctor_set(v___x_4357_, 1, v___x_4363_);
                    lean_ctor_set(v___x_4357_, 0, v___x_4362_);
                    v___x_4365_ = v___x_4357_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4362_);
                    lean_ctor_set(v_reuseFailAlloc_4373_, 1, v___x_4363_);
                    v___x_4365_ = v_reuseFailAlloc_4373_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4367_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if lean_obj_tag(v___y_4341_) == 1 {
                    v_val_4368_ = lean_ctor_get(v___y_4341_, 0);
                    lean_inc(v_val_4368_);
                    lean_dec_ref_known(v___y_4341_, 1);
                    v___x_4369_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    lean_inc(v___x_4360_);
                    v___x_4370_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4370_, 0, v___x_4360_);
                    lean_ctor_set(v___x_4370_, 1, v___x_4369_);
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
                    lean_dec(v___y_4341_);
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
                    v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4375_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_a_4376_);
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
                lean_dec(v___x_4385_);
                v_doElems_4396_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4397_ = l_Lean_Syntax_isIdent(v___x_4394_);
                if v___x_4397_ == 0 {
                    v___x_4398_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    lean_inc(v___x_4394_);
                    v___x_4399_ = l_Lean_Syntax_isOfKind(v___x_4394_, v___x_4398_);
                    if v___x_4399_ == 0 {
                        v___x_4400_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4394_,
                                v___x_4399_,
                                v___y_4392_,
                                v___y_4393_,
                            );
                        if lean_obj_tag(v___x_4400_) == 0 {
                            v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
                            lean_inc_n(v_a_4401_, 2);
                            v_a_4402_ = lean_ctor_get(v___x_4400_, 1);
                            lean_inc(v_a_4402_);
                            lean_dec_ref_known(v___x_4400_, 2);
                            v_ref_4403_ = lean_ctor_get(v___y_4392_, 5);
                            v___x_4404_ = l_Lean_SourceInfo_fromRef(v_ref_4403_, v___x_4399_);
                            v___x_4405_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4407_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4408_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4409_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            lean_inc_n(v___x_4404_, 15);
                            v___x_4410_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4410_, 0, v___x_4404_);
                            lean_ctor_set(v___x_4410_, 1, v___x_4409_);
                            v___x_4411_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4412_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_4412_, 0, v___x_4404_);
                            lean_ctor_set(v___x_4412_, 1, v___x_4406_);
                            lean_ctor_set(v___x_4412_, 2, v___x_4411_);
                            v___x_4413_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            lean_inc_ref_n(v___x_4412_, 4);
                            v___x_4414_ = l_Lean_Syntax_node2(
                                v___x_4404_,
                                v___x_4413_,
                                v___x_4412_,
                                v_a_4401_,
                            );
                            v___x_4415_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4414_);
                            v___x_4416_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4417_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4417_, 0, v___x_4404_);
                            lean_ctor_set(v___x_4417_, 1, v___x_4416_);
                            v___x_4418_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4419_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4421_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4421_, 0, v___x_4404_);
                            lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                            v___x_4422_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4394_);
                            v___x_4423_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4422_);
                            v___x_4424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4425_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4425_, 0, v___x_4404_);
                            lean_ctor_set(v___x_4425_, 1, v___x_4424_);
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
                            lean_dec(v___x_4395_);
                            lean_dec(v___x_4394_);
                            lean_dec(v_h_x3f_4391_);
                            lean_dec(v_body_4389_);
                            lean_dec_ref(v_decls_4339_);
                            lean_dec(v_tk_3944_);
                            v_a_4433_ = lean_ctor_get(v___x_4400_, 0);
                            v_a_4434_ = lean_ctor_get(v___x_4400_, 1);
                            v_isSharedCheck_4441_ = (!lean_is_exclusive(v___x_4400_)) as u8;
                            if v_isSharedCheck_4441_ == 0 {
                                v___x_4436_ = v___x_4400_;
                                v_isShared_4437_ = v_isSharedCheck_4441_;
                                state = 32;
                                continue;
                            } else {
                                lean_inc(v_a_4434_);
                                lean_inc(v_a_4433_);
                                lean_dec(v___x_4400_);
                                v___x_4436_ = lean_box(0);
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
                        lean_dec(v___x_4394_);
                        if lean_obj_tag(v___x_4442_) == 0 {
                            v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
                            lean_inc(v_a_4443_);
                            v_a_4444_ = lean_ctor_get(v___x_4442_, 1);
                            lean_inc(v_a_4444_);
                            lean_dec_ref_known(v___x_4442_, 2);
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
                            lean_dec(v___x_4395_);
                            lean_dec(v_h_x3f_4391_);
                            lean_dec(v_body_4389_);
                            lean_dec_ref(v_decls_4339_);
                            lean_dec(v_tk_3944_);
                            v_a_4445_ = lean_ctor_get(v___x_4442_, 0);
                            v_a_4446_ = lean_ctor_get(v___x_4442_, 1);
                            v_isSharedCheck_4453_ = (!lean_is_exclusive(v___x_4442_)) as u8;
                            if v_isSharedCheck_4453_ == 0 {
                                v___x_4448_ = v___x_4442_;
                                v_isShared_4449_ = v_isSharedCheck_4453_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_a_4446_);
                                lean_inc(v_a_4445_);
                                lean_dec(v___x_4442_);
                                v___x_4448_ = lean_box(0);
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
                    v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4433_);
                    lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_a_4434_);
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
                    v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4445_);
                    lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_a_4446_);
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
                lean_inc_ref(v___y_4471_);
                v___x_4478_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4478_, 0, v___y_4471_);
                lean_ctor_set(v___x_4478_, 1, v_body_4473_);
                v___x_4479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_4465_, v___x_4477_, v___x_4478_, v___y_4474_, v___y_4475_);
                if lean_obj_tag(v___x_4479_) == 0 {
                    v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
                    lean_inc(v_a_4480_);
                    v_a_4481_ = lean_ctor_get(v___x_4479_, 1);
                    lean_inc(v_a_4481_);
                    lean_dec_ref_known(v___x_4479_, 2);
                    v_fst_4482_ = lean_ctor_get(v_a_4480_, 0);
                    v_snd_4483_ = lean_ctor_get(v_a_4480_, 1);
                    v_isSharedCheck_4502_ = (!lean_is_exclusive(v_a_4480_)) as u8;
                    if v_isSharedCheck_4502_ == 0 {
                        v___x_4485_ = v_a_4480_;
                        v_isShared_4486_ = v_isSharedCheck_4502_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_snd_4483_);
                        lean_inc(v_fst_4482_);
                        lean_dec(v_a_4480_);
                        v___x_4485_ = lean_box(0);
                        v_isShared_4486_ = v_isSharedCheck_4502_;
                        state = 37;
                        continue;
                    }
                } else {
                    lean_dec(v_x_4472_);
                    lean_dec(v___y_4470_);
                    lean_dec(v___y_4469_);
                    lean_dec(v_tk_3944_);
                    v_a_4503_ = lean_ctor_get(v___x_4479_, 0);
                    v_a_4504_ = lean_ctor_get(v___x_4479_, 1);
                    v_isSharedCheck_4511_ = (!lean_is_exclusive(v___x_4479_)) as u8;
                    if v_isSharedCheck_4511_ == 0 {
                        v___x_4506_ = v___x_4479_;
                        v_isShared_4507_ = v_isSharedCheck_4511_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_4504_);
                        lean_inc(v_a_4503_);
                        lean_dec(v___x_4479_);
                        v___x_4506_ = lean_box(0);
                        v_isShared_4507_ = v_isSharedCheck_4511_;
                        state = 39;
                        continue;
                    }
                }
            }
            37 => {
                v_ref_4487_ = lean_ctor_get(v___y_4474_, 5);
                v___x_4488_ = l_Lean_SourceInfo_fromRef(v_ref_4487_, v___x_4465_);
                v___x_4489_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4490_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                lean_dec(v_tk_3944_);
                v___x_4491_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4486_ == 0 {
                    lean_ctor_set_tag(v___x_4485_, 2);
                    lean_ctor_set(v___x_4485_, 1, v___x_4491_);
                    lean_ctor_set(v___x_4485_, 0, v___x_4490_);
                    v___x_4493_ = v___x_4485_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4490_);
                    lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4491_);
                    v___x_4493_ = v_reuseFailAlloc_4501_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_4494_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4495_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if lean_obj_tag(v___y_4470_) == 1 {
                    v_val_4496_ = lean_ctor_get(v___y_4470_, 0);
                    lean_inc(v_val_4496_);
                    lean_dec_ref_known(v___y_4470_, 1);
                    v___x_4497_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    lean_inc(v___x_4488_);
                    v___x_4498_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4498_, 0, v___x_4488_);
                    lean_ctor_set(v___x_4498_, 1, v___x_4497_);
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
                    lean_dec(v___y_4470_);
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
                    v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4503_);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_a_4504_);
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
                lean_dec(v___x_4513_);
                v_doElems_4524_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4525_ = l_Lean_Syntax_isIdent(v___x_4522_);
                if v___x_4525_ == 0 {
                    v___x_4526_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    lean_inc(v___x_4522_);
                    v___x_4527_ = l_Lean_Syntax_isOfKind(v___x_4522_, v___x_4526_);
                    if v___x_4527_ == 0 {
                        v___x_4528_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4522_,
                                v___x_4527_,
                                v___y_4520_,
                                v___y_4521_,
                            );
                        if lean_obj_tag(v___x_4528_) == 0 {
                            v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
                            lean_inc_n(v_a_4529_, 2);
                            v_a_4530_ = lean_ctor_get(v___x_4528_, 1);
                            lean_inc(v_a_4530_);
                            lean_dec_ref_known(v___x_4528_, 2);
                            v_ref_4531_ = lean_ctor_get(v___y_4520_, 5);
                            v___x_4532_ = l_Lean_SourceInfo_fromRef(v_ref_4531_, v___x_4527_);
                            v___x_4533_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4535_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4536_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4537_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            lean_inc_n(v___x_4532_, 15);
                            v___x_4538_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4538_, 0, v___x_4532_);
                            lean_ctor_set(v___x_4538_, 1, v___x_4537_);
                            v___x_4539_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4540_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_4540_, 0, v___x_4532_);
                            lean_ctor_set(v___x_4540_, 1, v___x_4534_);
                            lean_ctor_set(v___x_4540_, 2, v___x_4539_);
                            v___x_4541_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            lean_inc_ref_n(v___x_4540_, 4);
                            v___x_4542_ = l_Lean_Syntax_node2(
                                v___x_4532_,
                                v___x_4541_,
                                v___x_4540_,
                                v_a_4529_,
                            );
                            v___x_4543_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4542_);
                            v___x_4544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4545_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4545_, 0, v___x_4532_);
                            lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                            v___x_4546_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4547_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4549_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4549_, 0, v___x_4532_);
                            lean_ctor_set(v___x_4549_, 1, v___x_4548_);
                            v___x_4550_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4522_);
                            v___x_4551_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4550_);
                            v___x_4552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4553_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4553_, 0, v___x_4532_);
                            lean_ctor_set(v___x_4553_, 1, v___x_4552_);
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
                            lean_dec(v___x_4523_);
                            lean_dec(v___x_4522_);
                            lean_dec(v_h_x3f_4519_);
                            lean_dec(v_body_4517_);
                            lean_dec_ref(v_decls_4467_);
                            lean_dec(v_tk_3944_);
                            v_a_4561_ = lean_ctor_get(v___x_4528_, 0);
                            v_a_4562_ = lean_ctor_get(v___x_4528_, 1);
                            v_isSharedCheck_4569_ = (!lean_is_exclusive(v___x_4528_)) as u8;
                            if v_isSharedCheck_4569_ == 0 {
                                v___x_4564_ = v___x_4528_;
                                v_isShared_4565_ = v_isSharedCheck_4569_;
                                state = 42;
                                continue;
                            } else {
                                lean_inc(v_a_4562_);
                                lean_inc(v_a_4561_);
                                lean_dec(v___x_4528_);
                                v___x_4564_ = lean_box(0);
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
                        lean_dec(v___x_4522_);
                        if lean_obj_tag(v___x_4570_) == 0 {
                            v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
                            lean_inc(v_a_4571_);
                            v_a_4572_ = lean_ctor_get(v___x_4570_, 1);
                            lean_inc(v_a_4572_);
                            lean_dec_ref_known(v___x_4570_, 2);
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
                            lean_dec(v___x_4523_);
                            lean_dec(v_h_x3f_4519_);
                            lean_dec(v_body_4517_);
                            lean_dec_ref(v_decls_4467_);
                            lean_dec(v_tk_3944_);
                            v_a_4573_ = lean_ctor_get(v___x_4570_, 0);
                            v_a_4574_ = lean_ctor_get(v___x_4570_, 1);
                            v_isSharedCheck_4581_ = (!lean_is_exclusive(v___x_4570_)) as u8;
                            if v_isSharedCheck_4581_ == 0 {
                                v___x_4576_ = v___x_4570_;
                                v_isShared_4577_ = v_isSharedCheck_4581_;
                                state = 44;
                                continue;
                            } else {
                                lean_inc(v_a_4574_);
                                lean_inc(v_a_4573_);
                                lean_dec(v___x_4570_);
                                v___x_4576_ = lean_box(0);
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
                    v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4561_);
                    lean_ctor_set(v_reuseFailAlloc_4568_, 1, v_a_4562_);
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
                    v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4573_);
                    lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_a_4574_);
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
    mut v_stx_4589_: *mut LeanObject,
    mut v_a_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4592_: *mut LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Lean_Elab_Do_expandDoFor(v_stx_4589_, v_a_4590_, v_a_4591_);
    lean_dec_ref(v_a_4590_);
    return v_res_4592_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(
    mut v___x_4593_: u8,
    mut v_inst_4594_: *mut LeanObject,
    mut v_R_4595_: *mut LeanObject,
    mut v_a_4596_: *mut LeanObject,
    mut v_b_4597_: *mut LeanObject,
    mut v_c_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_4602_: *mut LeanObject,
    mut v_inst_4603_: *mut LeanObject,
    mut v_R_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
    mut v_b_4606_: *mut LeanObject,
    mut v_c_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_148624__boxed_4610_: u8 = 0;
    let mut v_res_4611_: *mut LeanObject = core::ptr::null_mut();
    v___x_148624__boxed_4610_ = (lean_unbox(v___x_4602_) as u8);
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
    lean_dec_ref(v___y_4608_);
    return v_res_4611_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1()
-> *mut LeanObject {
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Lean_Elab_macroAttribute;
    v___x_4620_ = l_Lean_Elab_Do_expandDoFor___closed__1;
    v___x_4621_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1;
    v___x_4622_ = lean_alloc_closure(
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
    mut v_a_4624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4625_: *mut LeanObject = core::ptr::null_mut();
    v_res_4625_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
    return v_res_4625_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    v___x_4626_ = lean_box(0);
    v___x_4627_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4628_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    lean_ctor_set(v___x_4628_, 1, v___x_4626_);
    return v___x_4628_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    v___x_4630_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
    v___x_4631_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4631_, 0, v___x_4630_);
    return v___x_4631_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(
    mut v___y_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4633_: *mut LeanObject = core::ptr::null_mut();
    v_res_4633_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
    return v_res_4633_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(
    mut v_00_u03b1_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    v___x_4643_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
    return v___x_4643_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(
    mut v_00_u03b1_4644_: *mut LeanObject,
    mut v___y_4645_: *mut LeanObject,
    mut v___y_4646_: *mut LeanObject,
    mut v___y_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4653_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4651_);
    lean_dec_ref(v___y_4650_);
    lean_dec(v___y_4649_);
    lean_dec_ref(v___y_4648_);
    lean_dec(v___y_4647_);
    lean_dec_ref(v___y_4646_);
    lean_dec_ref(v___y_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(
    mut v_k_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v_b_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4662_);
    lean_inc_ref(v___y_4661_);
    lean_inc(v___y_4660_);
    lean_inc_ref(v___y_4659_);
    lean_inc(v___y_4657_);
    lean_inc_ref(v___y_4656_);
    lean_inc_ref(v___y_4655_);
    v___x_4664_ = lean_apply_9(
        v_k_4654_,
        v_b_4658_,
        v___y_4655_,
        v___y_4656_,
        v___y_4657_,
        v___y_4659_,
        v___y_4660_,
        v___y_4661_,
        v___y_4662_,
        lean_box(0),
    );
    return v___x_4664_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(
    mut v_k_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
    mut v___y_4668_: *mut LeanObject,
    mut v_b_4669_: *mut LeanObject,
    mut v___y_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4675_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4673_);
    lean_dec_ref(v___y_4672_);
    lean_dec(v___y_4671_);
    lean_dec_ref(v___y_4670_);
    lean_dec(v___y_4668_);
    lean_dec_ref(v___y_4667_);
    lean_dec_ref(v___y_4666_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
    mut v_name_4676_: *mut LeanObject,
    mut v_bi_4677_: u8,
    mut v_type_4678_: *mut LeanObject,
    mut v_k_4679_: *mut LeanObject,
    mut v_kind_4680_: u8,
    mut v___y_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
    mut v___y_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4683_);
                lean_inc_ref(v___y_4682_);
                lean_inc_ref(v___y_4681_);
                v___f_4689_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                lean_closure_set(v___f_4689_, 0, v_k_4679_);
                lean_closure_set(v___f_4689_, 1, v___y_4681_);
                lean_closure_set(v___f_4689_, 2, v___y_4682_);
                lean_closure_set(v___f_4689_, 3, v___y_4683_);
                v___x_4690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_4690_) == 0 {
                    return v___x_4690_;
                } else {
                    v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
                    v_isSharedCheck_4698_ = (!lean_is_exclusive(v___x_4690_)) as u8;
                    if v_isSharedCheck_4698_ == 0 {
                        v___x_4693_ = v___x_4690_;
                        v_isShared_4694_ = v_isSharedCheck_4698_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4691_);
                        lean_dec(v___x_4690_);
                        v___x_4693_ = lean_box(0);
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
                    v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
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
    mut v_name_4699_: *mut LeanObject,
    mut v_bi_4700_: *mut LeanObject,
    mut v_type_4701_: *mut LeanObject,
    mut v_k_4702_: *mut LeanObject,
    mut v_kind_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4712_: u8 = 0;
    let mut v_kind_boxed_4713_: u8 = 0;
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4712_ = (lean_unbox(v_bi_4700_) as u8);
    v_kind_boxed_4713_ = (lean_unbox(v_kind_4703_) as u8);
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
    lean_dec(v___y_4710_);
    lean_dec_ref(v___y_4709_);
    lean_dec(v___y_4708_);
    lean_dec_ref(v___y_4707_);
    lean_dec(v___y_4706_);
    lean_dec_ref(v___y_4705_);
    lean_dec_ref(v___y_4704_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(
    mut v_00_u03b1_4715_: *mut LeanObject,
    mut v_name_4716_: *mut LeanObject,
    mut v_bi_4717_: u8,
    mut v_type_4718_: *mut LeanObject,
    mut v_k_4719_: *mut LeanObject,
    mut v_kind_4720_: u8,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
    mut v___y_4724_: *mut LeanObject,
    mut v___y_4725_: *mut LeanObject,
    mut v___y_4726_: *mut LeanObject,
    mut v___y_4727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4730_: *mut LeanObject,
    mut v_name_4731_: *mut LeanObject,
    mut v_bi_4732_: *mut LeanObject,
    mut v_type_4733_: *mut LeanObject,
    mut v_k_4734_: *mut LeanObject,
    mut v_kind_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4744_: u8 = 0;
    let mut v_kind_boxed_4745_: u8 = 0;
    let mut v_res_4746_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4744_ = (lean_unbox(v_bi_4732_) as u8);
    v_kind_boxed_4745_ = (lean_unbox(v_kind_4735_) as u8);
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
    lean_dec(v___y_4742_);
    lean_dec_ref(v___y_4741_);
    lean_dec(v___y_4740_);
    lean_dec_ref(v___y_4739_);
    lean_dec(v___y_4738_);
    lean_dec_ref(v___y_4737_);
    lean_dec_ref(v___y_4736_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__0(
    mut v_a_4747_: *mut LeanObject,
    mut v_x_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
    mut v___y_4752_: *mut LeanObject,
    mut v___y_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    v___x_4757_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4757_, 0, v_a_4747_);
    return v___x_4757_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__0___boxed(
    mut v_a_4758_: *mut LeanObject,
    mut v_x_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
    mut v___y_4765_: *mut LeanObject,
    mut v___y_4766_: *mut LeanObject,
    mut v___y_4767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4768_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4766_);
    lean_dec_ref(v___y_4765_);
    lean_dec(v___y_4764_);
    lean_dec_ref(v___y_4763_);
    lean_dec(v___y_4762_);
    lean_dec_ref(v___y_4761_);
    lean_dec_ref(v___y_4760_);
    lean_dec_ref(v_x_4759_);
    return v_res_4768_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__2(
    mut v_x_4769_: *mut LeanObject,
    mut v___f_4770_: *mut LeanObject,
    mut v___x_4771_: *mut LeanObject,
    mut v_x_4772_: *mut LeanObject,
    mut v_x_4773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    v___x_4774_ = l_Lean_TSyntax_getId(v_x_4769_);
    v___x_4775_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4775_, 0, v___x_4774_);
    lean_ctor_set(v___x_4775_, 1, v___f_4770_);
    v___x_4776_ = lean_mk_empty_array_with_capacity(v___x_4771_);
    v___x_4777_ = lean_array_push(v___x_4776_, v___x_4775_);
    return v___x_4777_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__2___boxed(
    mut v_x_4778_: *mut LeanObject,
    mut v___f_4779_: *mut LeanObject,
    mut v___x_4780_: *mut LeanObject,
    mut v_x_4781_: *mut LeanObject,
    mut v_x_4782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4783_: *mut LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_Elab_Do_elabDoFor___lam__2(
        v_x_4778_,
        v___f_4779_,
        v___x_4780_,
        v_x_4781_,
        v_x_4782_,
    );
    lean_dec(v_x_4782_);
    lean_dec(v_x_4781_);
    lean_dec(v___x_4780_);
    lean_dec(v_x_4778_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__1(
    mut v_a_4784_: *mut LeanObject,
    mut v___x_4785_: *mut LeanObject,
    mut v___x_4786_: u8,
    mut v_r_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
    mut v___y_4794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    v_k_4796_ = lean_ctor_get(v_a_4784_, 1);
    lean_inc_ref(v_k_4796_);
    lean_dec_ref(v_a_4784_);
    lean_inc(v___y_4794_);
    lean_inc_ref(v___y_4793_);
    lean_inc(v___y_4792_);
    lean_inc_ref(v___y_4791_);
    lean_inc(v___y_4790_);
    lean_inc_ref(v___y_4789_);
    lean_inc_ref(v___y_4788_);
    lean_inc_ref(v_r_4787_);
    v___x_4797_ = lean_apply_9(
        v_k_4796_,
        v_r_4787_,
        v___y_4788_,
        v___y_4789_,
        v___y_4790_,
        v___y_4791_,
        v___y_4792_,
        v___y_4793_,
        v___y_4794_,
        lean_box(0),
    );
    if lean_obj_tag(v___x_4797_) == 0 {
        let mut v_a_4798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4801_: u8 = 0;
        let mut v___x_4802_: u8 = 0;
        let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
        v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
        lean_inc(v_a_4798_);
        lean_dec_ref_known(v___x_4797_, 1);
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
        lean_dec_ref(v___x_4800_);
        return v___x_4803_;
    } else {
        lean_dec_ref(v_r_4787_);
        return v___x_4797_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__1___boxed(
    mut v_a_4804_: *mut LeanObject,
    mut v___x_4805_: *mut LeanObject,
    mut v___x_4806_: *mut LeanObject,
    mut v_r_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
    mut v___y_4813_: *mut LeanObject,
    mut v___y_4814_: *mut LeanObject,
    mut v___y_4815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_71074__boxed_4816_: u8 = 0;
    let mut v_res_4817_: *mut LeanObject = core::ptr::null_mut();
    v___x_71074__boxed_4816_ = (lean_unbox(v___x_4806_) as u8);
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
    lean_dec(v___y_4814_);
    lean_dec_ref(v___y_4813_);
    lean_dec(v___y_4812_);
    lean_dec_ref(v___y_4811_);
    lean_dec(v___y_4810_);
    lean_dec_ref(v___y_4809_);
    lean_dec_ref(v___y_4808_);
    lean_dec(v___x_4805_);
    return v_res_4817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(
    mut v___x_4818_: *mut LeanObject,
    mut v_as_4819_: *mut LeanObject,
    mut v_sz_4820_: usize,
    mut v_i_4821_: usize,
    mut v_b_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: u8 = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
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
                v___x_4830_ = lean_usize_dec_lt(v_i_4821_, v_sz_4820_);
                if v___x_4830_ == 0 {
                    lean_dec_ref(v___x_4818_);
                    v___x_4831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4831_, 0, v_b_4822_);
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
                    if lean_obj_tag(v___x_4834_) == 0 {
                        v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
                        lean_inc_n(v_a_4835_, 2);
                        lean_dec_ref_known(v___x_4834_, 1);
                        v___x_4836_ = l_Lean_LocalDecl_toExpr(v_a_4835_);
                        v___x_4837_ = lean_box(0);
                        v___x_4838_ = lean_box(0);
                        v___x_4839_ = 0;
                        lean_inc_ref(v___x_4836_);
                        lean_inc(v_a_4832_);
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
                        if lean_obj_tag(v___x_4840_) == 0 {
                            lean_dec_ref_known(v___x_4840_, 1);
                            v___x_4841_ = l_Lean_LocalDecl_type(v_a_4835_);
                            lean_dec(v_a_4835_);
                            v___x_4842_ = l_Lean_Meta_getDecLevel(
                                v___x_4841_,
                                v___y_4825_,
                                v___y_4826_,
                                v___y_4827_,
                                v___y_4828_,
                            );
                            if lean_obj_tag(v___x_4842_) == 0 {
                                v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
                                lean_inc(v_a_4843_);
                                lean_dec_ref_known(v___x_4842_, 1);
                                v_u_4844_ = lean_ctor_get(v___x_4818_, 1);
                                lean_inc(v_u_4844_);
                                v___x_4845_ = l_Lean_Meta_isLevelDefEq(
                                    v_a_4843_,
                                    v_u_4844_,
                                    v___y_4825_,
                                    v___y_4826_,
                                    v___y_4827_,
                                    v___y_4828_,
                                );
                                if lean_obj_tag(v___x_4845_) == 0 {
                                    lean_dec_ref_known(v___x_4845_, 1);
                                    v___x_4846_ = lean_array_push(v_b_4822_, v___x_4836_);
                                    v___x_4847_ = 1usize;
                                    v___x_4848_ = lean_usize_add(v_i_4821_, v___x_4847_);
                                    v_i_4821_ = v___x_4848_;
                                    v_b_4822_ = v___x_4846_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_4836_);
                                    lean_dec_ref(v_b_4822_);
                                    lean_dec_ref(v___x_4818_);
                                    v_a_4850_ = lean_ctor_get(v___x_4845_, 0);
                                    v_isSharedCheck_4857_ = (!lean_is_exclusive(v___x_4845_)) as u8;
                                    if v_isSharedCheck_4857_ == 0 {
                                        v___x_4852_ = v___x_4845_;
                                        v_isShared_4853_ = v_isSharedCheck_4857_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4850_);
                                        lean_dec(v___x_4845_);
                                        v___x_4852_ = lean_box(0);
                                        v_isShared_4853_ = v_isSharedCheck_4857_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_4836_);
                                lean_dec_ref(v_b_4822_);
                                lean_dec_ref(v___x_4818_);
                                v_a_4858_ = lean_ctor_get(v___x_4842_, 0);
                                v_isSharedCheck_4865_ = (!lean_is_exclusive(v___x_4842_)) as u8;
                                if v_isSharedCheck_4865_ == 0 {
                                    v___x_4860_ = v___x_4842_;
                                    v_isShared_4861_ = v_isSharedCheck_4865_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_4858_);
                                    lean_dec(v___x_4842_);
                                    v___x_4860_ = lean_box(0);
                                    v_isShared_4861_ = v_isSharedCheck_4865_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4836_);
                            lean_dec(v_a_4835_);
                            lean_dec_ref(v_b_4822_);
                            lean_dec_ref(v___x_4818_);
                            v_a_4866_ = lean_ctor_get(v___x_4840_, 0);
                            v_isSharedCheck_4873_ = (!lean_is_exclusive(v___x_4840_)) as u8;
                            if v_isSharedCheck_4873_ == 0 {
                                v___x_4868_ = v___x_4840_;
                                v_isShared_4869_ = v_isSharedCheck_4873_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4866_);
                                lean_dec(v___x_4840_);
                                v___x_4868_ = lean_box(0);
                                v_isShared_4869_ = v_isSharedCheck_4873_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_4822_);
                        lean_dec_ref(v___x_4818_);
                        v_a_4874_ = lean_ctor_get(v___x_4834_, 0);
                        v_isSharedCheck_4881_ = (!lean_is_exclusive(v___x_4834_)) as u8;
                        if v_isSharedCheck_4881_ == 0 {
                            v___x_4876_ = v___x_4834_;
                            v_isShared_4877_ = v_isSharedCheck_4881_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4874_);
                            lean_dec(v___x_4834_);
                            v___x_4876_ = lean_box(0);
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
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(
    mut v___x_4882_: *mut LeanObject,
    mut v_as_4883_: *mut LeanObject,
    mut v_sz_4884_: *mut LeanObject,
    mut v_i_4885_: *mut LeanObject,
    mut v_b_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
    mut v___y_4892_: *mut LeanObject,
    mut v___y_4893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4894_: usize = 0;
    let mut v_i_boxed_4895_: usize = 0;
    let mut v_res_4896_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4894_ = lean_unbox_usize(v_sz_4884_);
    lean_dec(v_sz_4884_);
    v_i_boxed_4895_ = lean_unbox_usize(v_i_4885_);
    lean_dec(v_i_4885_);
    v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_4882_, v_as_4883_, v_sz_boxed_4894_, v_i_boxed_4895_, v_b_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
    lean_dec(v___y_4892_);
    lean_dec_ref(v___y_4891_);
    lean_dec(v___y_4890_);
    lean_dec_ref(v___y_4889_);
    lean_dec(v___y_4888_);
    lean_dec_ref(v___y_4887_);
    lean_dec_ref(v_as_4883_);
    return v_res_4896_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(
    mut v_msgData_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    v___x_4903_ = lean_st_ref_get(v___y_4901_);
    v_env_4904_ = lean_ctor_get(v___x_4903_, 0);
    lean_inc_ref(v_env_4904_);
    lean_dec(v___x_4903_);
    v___x_4905_ = lean_st_ref_get(v___y_4899_);
    v_mctx_4906_ = lean_ctor_get(v___x_4905_, 0);
    lean_inc_ref(v_mctx_4906_);
    lean_dec(v___x_4905_);
    v_lctx_4907_ = lean_ctor_get(v___y_4898_, 2);
    v_options_4908_ = lean_ctor_get(v___y_4900_, 2);
    lean_inc_ref(v_options_4908_);
    lean_inc_ref(v_lctx_4907_);
    v___x_4909_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4909_, 0, v_env_4904_);
    lean_ctor_set(v___x_4909_, 1, v_mctx_4906_);
    lean_ctor_set(v___x_4909_, 2, v_lctx_4907_);
    lean_ctor_set(v___x_4909_, 3, v_options_4908_);
    v___x_4910_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4910_, 0, v___x_4909_);
    lean_ctor_set(v___x_4910_, 1, v_msgData_4897_);
    v___x_4911_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4911_, 0, v___x_4910_);
    return v___x_4911_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(
    mut v_msgData_4912_: *mut LeanObject,
    mut v___y_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
    mut v___y_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4918_: *mut LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
    lean_dec(v___y_4916_);
    lean_dec_ref(v___y_4915_);
    lean_dec(v___y_4914_);
    lean_dec_ref(v___y_4913_);
    return v_res_4918_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    v___x_4919_ = lean_box(1);
    v___x_4920_ = l_Lean_MessageData_ofFormat(v___x_4919_);
    return v___x_4920_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    v___x_4924_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2;
    v___x_4925_ = l_Lean_MessageData_ofFormat(v___x_4924_);
    return v___x_4925_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(
    mut v_x_4926_: *mut LeanObject,
    mut v_x_4927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4932_: u8 = 0;
    let mut v_before_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_unused_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4927_) == 0 {
                    return v_x_4926_;
                } else {
                    v_head_4928_ = lean_ctor_get(v_x_4927_, 0);
                    v_tail_4929_ = lean_ctor_get(v_x_4927_, 1);
                    v_isSharedCheck_4951_ = (!lean_is_exclusive(v_x_4927_)) as u8;
                    if v_isSharedCheck_4951_ == 0 {
                        v___x_4931_ = v_x_4927_;
                        v_isShared_4932_ = v_isSharedCheck_4951_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4929_);
                        lean_inc(v_head_4928_);
                        lean_dec(v_x_4927_);
                        v___x_4931_ = lean_box(0);
                        v_isShared_4932_ = v_isSharedCheck_4951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4933_ = lean_ctor_get(v_head_4928_, 0);
                v_isSharedCheck_4949_ = (!lean_is_exclusive(v_head_4928_)) as u8;
                if v_isSharedCheck_4949_ == 0 {
                    v_unused_4950_ = lean_ctor_get(v_head_4928_, 1);
                    lean_dec(v_unused_4950_);
                    v___x_4935_ = v_head_4928_;
                    v_isShared_4936_ = v_isSharedCheck_4949_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_4933_);
                    lean_dec(v_head_4928_);
                    v___x_4935_ = lean_box(0);
                    v_isShared_4936_ = v_isSharedCheck_4949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4937_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
                if v_isShared_4936_ == 0 {
                    lean_ctor_set_tag(v___x_4935_, 7);
                    lean_ctor_set(v___x_4935_, 1, v___x_4937_);
                    lean_ctor_set(v___x_4935_, 0, v_x_4926_);
                    v___x_4939_ = v___x_4935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_x_4926_);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 1, v___x_4937_);
                    v___x_4939_ = v_reuseFailAlloc_4948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4940_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
                if v_isShared_4932_ == 0 {
                    lean_ctor_set_tag(v___x_4931_, 7);
                    lean_ctor_set(v___x_4931_, 1, v___x_4940_);
                    lean_ctor_set(v___x_4931_, 0, v___x_4939_);
                    v___x_4942_ = v___x_4931_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4939_);
                    lean_ctor_set(v_reuseFailAlloc_4947_, 1, v___x_4940_);
                    v___x_4942_ = v_reuseFailAlloc_4947_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4943_ = l_Lean_MessageData_ofSyntax(v_before_4933_);
                v___x_4944_ = l_Lean_indentD(v___x_4943_);
                v___x_4945_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4945_, 0, v___x_4942_);
                lean_ctor_set(v___x_4945_, 1, v___x_4944_);
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
    mut v_opts_4952_: *mut LeanObject,
    mut v_opt_4953_: *mut LeanObject,
) -> u8 {
    let mut v_name_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    v_name_4954_ = lean_ctor_get(v_opt_4953_, 0);
    v_defValue_4955_ = lean_ctor_get(v_opt_4953_, 1);
    v_map_4956_ = lean_ctor_get(v_opts_4952_, 0);
    v___x_4957_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4956_,
            v_name_4954_,
        );
    if lean_obj_tag(v___x_4957_) == 0 {
        let mut v___x_4958_: u8 = 0;
        v___x_4958_ = (lean_unbox(v_defValue_4955_) as u8);
        return v___x_4958_;
    } else {
        let mut v_val_4959_: *mut LeanObject = core::ptr::null_mut();
        v_val_4959_ = lean_ctor_get(v___x_4957_, 0);
        lean_inc(v_val_4959_);
        lean_dec_ref_known(v___x_4957_, 1);
        if lean_obj_tag(v_val_4959_) == 1 {
            let mut v_v_4960_: u8 = 0;
            v_v_4960_ = lean_ctor_get_uint8(v_val_4959_, 0 as u32);
            lean_dec_ref_known(v_val_4959_, 0);
            return v_v_4960_;
        } else {
            let mut v___x_4961_: u8 = 0;
            lean_dec(v_val_4959_);
            v___x_4961_ = (lean_unbox(v_defValue_4955_) as u8);
            return v___x_4961_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(
    mut v_opts_4962_: *mut LeanObject,
    mut v_opt_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4964_: u8 = 0;
    let mut v_r_4965_: *mut LeanObject = core::ptr::null_mut();
    v_res_4964_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_4962_, v_opt_4963_);
    lean_dec_ref(v_opt_4963_);
    lean_dec_ref(v_opts_4962_);
    v_r_4965_ = lean_box((v_res_4964_) as usize);
    return v_r_4965_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    v___x_4969_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1;
    v___x_4970_ = l_Lean_MessageData_ofFormat(v___x_4969_);
    return v___x_4970_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(
    mut v_msgData_4971_: *mut LeanObject,
    mut v_macroStack_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: u8 = 0;
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_unused_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4975_ = lean_ctor_get(v___y_4973_, 2);
                v___x_4976_ = l_Lean_Elab_pp_macroStack;
                v___x_4977_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_4975_, v___x_4976_);
                if v___x_4977_ == 0 {
                    lean_dec(v_macroStack_4972_);
                    v___x_4978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4978_, 0, v_msgData_4971_);
                    return v___x_4978_;
                } else {
                    if lean_obj_tag(v_macroStack_4972_) == 0 {
                        v___x_4979_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4979_, 0, v_msgData_4971_);
                        return v___x_4979_;
                    } else {
                        v_head_4980_ = lean_ctor_get(v_macroStack_4972_, 0);
                        lean_inc(v_head_4980_);
                        v_after_4981_ = lean_ctor_get(v_head_4980_, 1);
                        v_isSharedCheck_4996_ = (!lean_is_exclusive(v_head_4980_)) as u8;
                        if v_isSharedCheck_4996_ == 0 {
                            v_unused_4997_ = lean_ctor_get(v_head_4980_, 0);
                            lean_dec(v_unused_4997_);
                            v___x_4983_ = v_head_4980_;
                            v_isShared_4984_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_4981_);
                            lean_dec(v_head_4980_);
                            v___x_4983_ = lean_box(0);
                            v_isShared_4984_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4985_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
                if v_isShared_4984_ == 0 {
                    lean_ctor_set_tag(v___x_4983_, 7);
                    lean_ctor_set(v___x_4983_, 1, v___x_4985_);
                    lean_ctor_set(v___x_4983_, 0, v_msgData_4971_);
                    v___x_4987_ = v___x_4983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4995_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_msgData_4971_);
                    lean_ctor_set(v_reuseFailAlloc_4995_, 1, v___x_4985_);
                    v___x_4987_ = v_reuseFailAlloc_4995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4988_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
                v___x_4989_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4989_, 0, v___x_4987_);
                lean_ctor_set(v___x_4989_, 1, v___x_4988_);
                v___x_4990_ = l_Lean_MessageData_ofSyntax(v_after_4981_);
                v___x_4991_ = l_Lean_indentD(v___x_4990_);
                v_msgData_4992_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_4992_, 0, v___x_4989_);
                lean_ctor_set(v_msgData_4992_, 1, v___x_4991_);
                v___x_4993_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_4992_, v_macroStack_4972_);
                v___x_4994_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4994_, 0, v___x_4993_);
                return v___x_4994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(
    mut v_msgData_4998_: *mut LeanObject,
    mut v_macroStack_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5002_: *mut LeanObject = core::ptr::null_mut();
    v_res_5002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_4998_, v_macroStack_4999_, v___y_5000_);
    lean_dec_ref(v___y_5000_);
    return v_res_5002_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
    mut v_msg_5003_: *mut LeanObject,
    mut v___y_5004_: *mut LeanObject,
    mut v___y_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5011_ = lean_ctor_get(v___y_5008_, 5);
                v___x_5012_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_5003_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
                v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
                lean_inc(v_a_5013_);
                lean_dec_ref(v___x_5012_);
                v_macroStack_5014_ = lean_ctor_get(v___y_5004_, 1);
                v___x_5015_ = l_Lean_Elab_getBetterRef(v_ref_5011_, v_macroStack_5014_);
                lean_inc(v_macroStack_5014_);
                v___x_5016_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_5013_, v_macroStack_5014_, v___y_5008_);
                v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
                v_isSharedCheck_5025_ = (!lean_is_exclusive(v___x_5016_)) as u8;
                if v_isSharedCheck_5025_ == 0 {
                    v___x_5019_ = v___x_5016_;
                    v_isShared_5020_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5017_);
                    lean_dec(v___x_5016_);
                    v___x_5019_ = lean_box(0);
                    v_isShared_5020_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5021_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5021_, 0, v___x_5015_);
                lean_ctor_set(v___x_5021_, 1, v_a_5017_);
                if v_isShared_5020_ == 0 {
                    lean_ctor_set_tag(v___x_5019_, 1);
                    lean_ctor_set(v___x_5019_, 0, v___x_5021_);
                    v___x_5023_ = v___x_5019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
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
    mut v_msg_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5034_: *mut LeanObject = core::ptr::null_mut();
    v_res_5034_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
        v_msg_5026_,
        v___y_5027_,
        v___y_5028_,
        v___y_5029_,
        v___y_5030_,
        v___y_5031_,
        v___y_5032_,
    );
    lean_dec(v___y_5032_);
    lean_dec_ref(v___y_5031_);
    lean_dec(v___y_5030_);
    lean_dec_ref(v___y_5029_);
    lean_dec(v___y_5028_);
    lean_dec_ref(v___y_5027_);
    return v_res_5034_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3() -> *mut LeanObject {
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    v___x_5040_ = lean_box(0);
    v___x_5041_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__2;
    v___x_5042_ = l_Lean_mkConst(v___x_5041_, v___x_5040_);
    return v___x_5042_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5() -> *mut LeanObject {
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    v___x_5044_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__4;
    v___x_5045_ = l_Lean_stringToMessageData(v___x_5044_);
    return v___x_5045_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7() -> *mut LeanObject {
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    v___x_5047_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__6;
    v___x_5048_ = l_Lean_stringToMessageData(v___x_5047_);
    return v___x_5048_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10() -> *mut LeanObject {
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__9;
    v___x_5053_ = l_Lean_MessageData_ofFormat(v___x_5052_);
    return v___x_5053_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__3(
    mut v___y_5054_: *mut LeanObject,
    mut v_monadInfo_5055_: *mut LeanObject,
    mut v_returnsEarly_5056_: u8,
    mut v___x_5057_: *mut LeanObject,
    mut v_a_5058_: *mut LeanObject,
    mut v___x_5059_: u8,
    mut v_e_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
    mut v___y_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defs_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5076_: usize = 0;
    let mut v___x_5077_: usize = 0;
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5084_: u8 = 0;
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_unused_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_returnVar_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut v_val_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut v___y_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5092_ = lean_mk_empty_array_with_capacity(v___x_5057_);
                if lean_obj_tag(v_e_5060_) == 0 {
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
                if lean_obj_tag(v___x_5078_) == 0 {
                    if v_returnsEarly_5056_ == 0 {
                        return v___x_5078_;
                    } else {
                        v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
                        lean_inc(v_a_5079_);
                        v___x_5080_ = lean_array_get_size(v___y_5054_);
                        v___x_5081_ = lean_nat_dec_eq(v___x_5080_, v___x_5057_);
                        if v___x_5081_ == 0 {
                            lean_dec(v_a_5079_);
                            return v___x_5078_;
                        } else {
                            v_isSharedCheck_5090_ = (!lean_is_exclusive(v___x_5078_)) as u8;
                            if v_isSharedCheck_5090_ == 0 {
                                v_unused_5091_ = lean_ctor_get(v___x_5078_, 0);
                                lean_dec(v_unused_5091_);
                                v___x_5083_ = v___x_5078_;
                                v_isShared_5084_ = v_isSharedCheck_5090_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v___x_5078_);
                                v___x_5083_ = lean_box(0);
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
                v___x_5085_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once),
                    _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3,
                );
                v___x_5086_ = lean_array_push(v_a_5079_, v___x_5085_);
                if v_isShared_5084_ == 0 {
                    lean_ctor_set(v___x_5083_, 0, v___x_5086_);
                    v___x_5088_ = v___x_5083_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
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
                    lean_dec(v_e_5060_);
                    lean_dec_ref(v_a_5058_);
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
                    if lean_obj_tag(v_e_5060_) == 0 {
                        v_resultType_5103_ = lean_ctor_get(v_a_5058_, 0);
                        lean_inc_ref(v_resultType_5103_);
                        lean_dec_ref(v_a_5058_);
                        v___x_5104_ = l_Lean_Meta_mkNone(
                            v_resultType_5103_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                        );
                        if lean_obj_tag(v___x_5104_) == 0 {
                            v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
                            lean_inc(v_a_5105_);
                            lean_dec_ref_known(v___x_5104_, 1);
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
                            lean_dec_ref(v___x_5092_);
                            lean_dec_ref(v_monadInfo_5055_);
                            v_a_5106_ = lean_ctor_get(v___x_5104_, 0);
                            v_isSharedCheck_5113_ = (!lean_is_exclusive(v___x_5104_)) as u8;
                            if v_isSharedCheck_5113_ == 0 {
                                v___x_5108_ = v___x_5104_;
                                v_isShared_5109_ = v_isSharedCheck_5113_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5106_);
                                lean_dec(v___x_5104_);
                                v___x_5108_ = lean_box(0);
                                v_isShared_5109_ = v_isSharedCheck_5113_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_val_5114_ = lean_ctor_get(v_e_5060_, 0);
                        lean_inc(v_val_5114_);
                        lean_dec_ref_known(v_e_5060_, 1);
                        v_resultType_5115_ = lean_ctor_get(v_a_5058_, 0);
                        lean_inc_ref(v_resultType_5115_);
                        lean_dec_ref(v_a_5058_);
                        v___x_5116_ = l_Lean_Meta_mkSome(
                            v_resultType_5115_,
                            v_val_5114_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                        );
                        if lean_obj_tag(v___x_5116_) == 0 {
                            v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
                            lean_inc(v_a_5117_);
                            lean_dec_ref_known(v___x_5116_, 1);
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
                            lean_dec_ref(v___x_5092_);
                            lean_dec_ref(v_monadInfo_5055_);
                            v_a_5118_ = lean_ctor_get(v___x_5116_, 0);
                            v_isSharedCheck_5125_ = (!lean_is_exclusive(v___x_5116_)) as u8;
                            if v_isSharedCheck_5125_ == 0 {
                                v___x_5120_ = v___x_5116_;
                                v_isShared_5121_ = v_isSharedCheck_5125_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_5118_);
                                lean_dec(v___x_5116_);
                                v___x_5120_ = lean_box(0);
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
                    v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
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
                    v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
                    v___x_5123_ = v_reuseFailAlloc_5124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5123_;
            }
            10 => {
                lean_inc_ref(v___y_5127_);
                v___x_5129_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5129_, 0, v___y_5127_);
                lean_ctor_set(v___x_5129_, 1, v___y_5128_);
                v___x_5130_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once),
                    _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5,
                );
                v___x_5131_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                v___x_5132_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
                    v___x_5131_,
                    v___y_5061_,
                    v___y_5062_,
                    v___y_5063_,
                    v___y_5064_,
                    v___y_5065_,
                    v___y_5066_,
                );
                v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
                v_isSharedCheck_5140_ = (!lean_is_exclusive(v___x_5132_)) as u8;
                if v_isSharedCheck_5140_ == 0 {
                    v___x_5135_ = v___x_5132_;
                    v_isShared_5136_ = v_isSharedCheck_5140_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_5133_);
                    lean_dec(v___x_5132_);
                    v___x_5135_ = lean_box(0);
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
                    v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
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
                    lean_dec_ref(v___x_5092_);
                    lean_dec_ref(v_a_5058_);
                    lean_dec_ref(v_monadInfo_5055_);
                    v___x_5142_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once),
                        _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7,
                    );
                    if lean_obj_tag(v_e_5060_) == 0 {
                        v___x_5143_ = lean_obj_once(
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
                        v_val_5144_ = lean_ctor_get(v_e_5060_, 0);
                        lean_inc(v_val_5144_);
                        lean_dec_ref_known(v_e_5060_, 1);
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
    mut v___y_5146_: *mut LeanObject,
    mut v_monadInfo_5147_: *mut LeanObject,
    mut v_returnsEarly_5148_: *mut LeanObject,
    mut v___x_5149_: *mut LeanObject,
    mut v_a_5150_: *mut LeanObject,
    mut v___x_5151_: *mut LeanObject,
    mut v_e_5152_: *mut LeanObject,
    mut v___y_5153_: *mut LeanObject,
    mut v___y_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_returnsEarly_boxed_5160_: u8 = 0;
    let mut v___x_71505__boxed_5161_: u8 = 0;
    let mut v_res_5162_: *mut LeanObject = core::ptr::null_mut();
    v_returnsEarly_boxed_5160_ = (lean_unbox(v_returnsEarly_5148_) as u8);
    v___x_71505__boxed_5161_ = (lean_unbox(v___x_5151_) as u8);
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
    lean_dec(v___y_5158_);
    lean_dec_ref(v___y_5157_);
    lean_dec(v___y_5156_);
    lean_dec_ref(v___y_5155_);
    lean_dec(v___y_5154_);
    lean_dec_ref(v___y_5153_);
    lean_dec(v___x_5149_);
    lean_dec_ref(v___y_5146_);
    return v_res_5162_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__4(
    mut v___f_5164_: *mut LeanObject,
    mut v_u_5165_: *mut LeanObject,
    mut v___x_5166_: *mut LeanObject,
    mut v___x_5167_: *mut LeanObject,
    mut v_snd_5168_: *mut LeanObject,
    mut v___x_5169_: *mut LeanObject,
    mut v_e_5170_: *mut LeanObject,
    mut v___y_5171_: *mut LeanObject,
    mut v___y_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
    mut v___y_5176_: *mut LeanObject,
    mut v___y_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5193_: u8 = 0;
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_a_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5179_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5179_, 0, v_e_5170_);
                lean_inc(v___y_5177_);
                lean_inc_ref(v___y_5176_);
                lean_inc(v___y_5175_);
                lean_inc_ref(v___y_5174_);
                lean_inc(v___y_5173_);
                lean_inc_ref(v___y_5172_);
                v___x_5180_ = lean_apply_8(
                    v___f_5164_,
                    v___x_5179_,
                    v___y_5172_,
                    v___y_5173_,
                    v___y_5174_,
                    v___y_5175_,
                    v___y_5176_,
                    v___y_5177_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5180_) == 0 {
                    v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
                    lean_inc(v_a_5181_);
                    lean_dec_ref_known(v___x_5180_, 1);
                    v___x_5182_ = l_Lean_Meta_mkProdMkN(
                        v_a_5181_,
                        v_u_5165_,
                        v___y_5174_,
                        v___y_5175_,
                        v___y_5176_,
                        v___y_5177_,
                    );
                    if lean_obj_tag(v___x_5182_) == 0 {
                        v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
                        lean_inc(v_a_5183_);
                        lean_dec_ref_known(v___x_5182_, 1);
                        v_fst_5184_ = lean_ctor_get(v_a_5183_, 0);
                        lean_inc(v_fst_5184_);
                        lean_dec(v_a_5183_);
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
                        lean_dec_ref(v___x_5169_);
                        lean_dec_ref(v_snd_5168_);
                        lean_dec(v___x_5167_);
                        lean_dec_ref(v___x_5166_);
                        v_a_5190_ = lean_ctor_get(v___x_5182_, 0);
                        v_isSharedCheck_5197_ = (!lean_is_exclusive(v___x_5182_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5192_ = v___x_5182_;
                            v_isShared_5193_ = v_isSharedCheck_5197_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5190_);
                            lean_dec(v___x_5182_);
                            v___x_5192_ = lean_box(0);
                            v_isShared_5193_ = v_isSharedCheck_5197_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5169_);
                    lean_dec_ref(v_snd_5168_);
                    lean_dec(v___x_5167_);
                    lean_dec_ref(v___x_5166_);
                    lean_dec(v_u_5165_);
                    v_a_5198_ = lean_ctor_get(v___x_5180_, 0);
                    v_isSharedCheck_5205_ = (!lean_is_exclusive(v___x_5180_)) as u8;
                    if v_isSharedCheck_5205_ == 0 {
                        v___x_5200_ = v___x_5180_;
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5198_);
                        lean_dec(v___x_5180_);
                        v___x_5200_ = lean_box(0);
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
                    v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
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
                    v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
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
    mut v___f_5206_: *mut LeanObject,
    mut v_u_5207_: *mut LeanObject,
    mut v___x_5208_: *mut LeanObject,
    mut v___x_5209_: *mut LeanObject,
    mut v_snd_5210_: *mut LeanObject,
    mut v___x_5211_: *mut LeanObject,
    mut v_e_5212_: *mut LeanObject,
    mut v___y_5213_: *mut LeanObject,
    mut v___y_5214_: *mut LeanObject,
    mut v___y_5215_: *mut LeanObject,
    mut v___y_5216_: *mut LeanObject,
    mut v___y_5217_: *mut LeanObject,
    mut v___y_5218_: *mut LeanObject,
    mut v___y_5219_: *mut LeanObject,
    mut v___y_5220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5221_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5219_);
    lean_dec_ref(v___y_5218_);
    lean_dec(v___y_5217_);
    lean_dec_ref(v___y_5216_);
    lean_dec(v___y_5215_);
    lean_dec_ref(v___y_5214_);
    lean_dec_ref(v___y_5213_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__5(
    mut v___f_5223_: *mut LeanObject,
    mut v___x_5224_: *mut LeanObject,
    mut v_u_5225_: *mut LeanObject,
    mut v___x_5226_: *mut LeanObject,
    mut v___x_5227_: *mut LeanObject,
    mut v_snd_5228_: *mut LeanObject,
    mut v___x_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5236_);
                lean_inc_ref(v___y_5235_);
                lean_inc(v___y_5234_);
                lean_inc_ref(v___y_5233_);
                lean_inc(v___y_5232_);
                lean_inc_ref(v___y_5231_);
                v___x_5238_ = lean_apply_8(
                    v___f_5223_,
                    v___x_5224_,
                    v___y_5231_,
                    v___y_5232_,
                    v___y_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5238_) == 0 {
                    v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
                    lean_inc(v_a_5239_);
                    lean_dec_ref_known(v___x_5238_, 1);
                    v___x_5240_ = l_Lean_Meta_mkProdMkN(
                        v_a_5239_,
                        v_u_5225_,
                        v___y_5233_,
                        v___y_5234_,
                        v___y_5235_,
                        v___y_5236_,
                    );
                    if lean_obj_tag(v___x_5240_) == 0 {
                        v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
                        lean_inc(v_a_5241_);
                        lean_dec_ref_known(v___x_5240_, 1);
                        v_fst_5242_ = lean_ctor_get(v_a_5241_, 0);
                        lean_inc(v_fst_5242_);
                        lean_dec(v_a_5241_);
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
                        lean_dec_ref(v___x_5229_);
                        lean_dec_ref(v_snd_5228_);
                        lean_dec(v___x_5227_);
                        lean_dec_ref(v___x_5226_);
                        v_a_5248_ = lean_ctor_get(v___x_5240_, 0);
                        v_isSharedCheck_5255_ = (!lean_is_exclusive(v___x_5240_)) as u8;
                        if v_isSharedCheck_5255_ == 0 {
                            v___x_5250_ = v___x_5240_;
                            v_isShared_5251_ = v_isSharedCheck_5255_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5248_);
                            lean_dec(v___x_5240_);
                            v___x_5250_ = lean_box(0);
                            v_isShared_5251_ = v_isSharedCheck_5255_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5229_);
                    lean_dec_ref(v_snd_5228_);
                    lean_dec(v___x_5227_);
                    lean_dec_ref(v___x_5226_);
                    lean_dec(v_u_5225_);
                    v_a_5256_ = lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5263_ = (!lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5263_ == 0 {
                        v___x_5258_ = v___x_5238_;
                        v_isShared_5259_ = v_isSharedCheck_5263_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5256_);
                        lean_dec(v___x_5238_);
                        v___x_5258_ = lean_box(0);
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
                    v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
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
                    v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
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
    mut v___f_5264_: *mut LeanObject,
    mut v___x_5265_: *mut LeanObject,
    mut v_u_5266_: *mut LeanObject,
    mut v___x_5267_: *mut LeanObject,
    mut v___x_5268_: *mut LeanObject,
    mut v_snd_5269_: *mut LeanObject,
    mut v___x_5270_: *mut LeanObject,
    mut v___y_5271_: *mut LeanObject,
    mut v___y_5272_: *mut LeanObject,
    mut v___y_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5279_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5277_);
    lean_dec_ref(v___y_5276_);
    lean_dec(v___y_5275_);
    lean_dec_ref(v___y_5274_);
    lean_dec(v___y_5273_);
    lean_dec_ref(v___y_5272_);
    lean_dec_ref(v___y_5271_);
    return v_res_5279_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__6(
    mut v___f_5280_: *mut LeanObject,
    mut v___x_5281_: *mut LeanObject,
    mut v_u_5282_: *mut LeanObject,
    mut v___x_5283_: *mut LeanObject,
    mut v___x_5284_: *mut LeanObject,
    mut v_snd_5285_: *mut LeanObject,
    mut v___x_5286_: *mut LeanObject,
    mut v___y_5287_: *mut LeanObject,
    mut v___y_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
    mut v___y_5291_: *mut LeanObject,
    mut v___y_5292_: *mut LeanObject,
    mut v___y_5293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5293_);
                lean_inc_ref(v___y_5292_);
                lean_inc(v___y_5291_);
                lean_inc_ref(v___y_5290_);
                lean_inc(v___y_5289_);
                lean_inc_ref(v___y_5288_);
                v___x_5295_ = lean_apply_8(
                    v___f_5280_,
                    v___x_5281_,
                    v___y_5288_,
                    v___y_5289_,
                    v___y_5290_,
                    v___y_5291_,
                    v___y_5292_,
                    v___y_5293_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5295_) == 0 {
                    v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
                    lean_inc(v_a_5296_);
                    lean_dec_ref_known(v___x_5295_, 1);
                    v___x_5297_ = l_Lean_Meta_mkProdMkN(
                        v_a_5296_,
                        v_u_5282_,
                        v___y_5290_,
                        v___y_5291_,
                        v___y_5292_,
                        v___y_5293_,
                    );
                    if lean_obj_tag(v___x_5297_) == 0 {
                        v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
                        lean_inc(v_a_5298_);
                        lean_dec_ref_known(v___x_5297_, 1);
                        v_fst_5299_ = lean_ctor_get(v_a_5298_, 0);
                        lean_inc(v_fst_5299_);
                        lean_dec(v_a_5298_);
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
                        lean_dec_ref(v___x_5286_);
                        lean_dec_ref(v_snd_5285_);
                        lean_dec(v___x_5284_);
                        lean_dec_ref(v___x_5283_);
                        v_a_5305_ = lean_ctor_get(v___x_5297_, 0);
                        v_isSharedCheck_5312_ = (!lean_is_exclusive(v___x_5297_)) as u8;
                        if v_isSharedCheck_5312_ == 0 {
                            v___x_5307_ = v___x_5297_;
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5305_);
                            lean_dec(v___x_5297_);
                            v___x_5307_ = lean_box(0);
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5286_);
                    lean_dec_ref(v_snd_5285_);
                    lean_dec(v___x_5284_);
                    lean_dec_ref(v___x_5283_);
                    lean_dec(v_u_5282_);
                    v_a_5313_ = lean_ctor_get(v___x_5295_, 0);
                    v_isSharedCheck_5320_ = (!lean_is_exclusive(v___x_5295_)) as u8;
                    if v_isSharedCheck_5320_ == 0 {
                        v___x_5315_ = v___x_5295_;
                        v_isShared_5316_ = v_isSharedCheck_5320_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5313_);
                        lean_dec(v___x_5295_);
                        v___x_5315_ = lean_box(0);
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
                    v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
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
                    v_reuseFailAlloc_5319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
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
    mut v___f_5321_: *mut LeanObject,
    mut v___x_5322_: *mut LeanObject,
    mut v_u_5323_: *mut LeanObject,
    mut v___x_5324_: *mut LeanObject,
    mut v___x_5325_: *mut LeanObject,
    mut v_snd_5326_: *mut LeanObject,
    mut v___x_5327_: *mut LeanObject,
    mut v___y_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
    mut v___y_5330_: *mut LeanObject,
    mut v___y_5331_: *mut LeanObject,
    mut v___y_5332_: *mut LeanObject,
    mut v___y_5333_: *mut LeanObject,
    mut v___y_5334_: *mut LeanObject,
    mut v___y_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5336_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5334_);
    lean_dec_ref(v___y_5333_);
    lean_dec(v___y_5332_);
    lean_dec_ref(v___y_5331_);
    lean_dec(v___y_5330_);
    lean_dec_ref(v___y_5329_);
    lean_dec_ref(v___y_5328_);
    return v_res_5336_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__7(
    mut v___x_5337_: *mut LeanObject,
    mut v___f_5338_: *mut LeanObject,
    mut v___f_5339_: *mut LeanObject,
    mut v___x_5340_: *mut LeanObject,
    mut v___x_5341_: *mut LeanObject,
    mut v___y_5342_: *mut LeanObject,
    mut v___y_5343_: *mut LeanObject,
    mut v___y_5344_: *mut LeanObject,
    mut v___y_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
    mut v___y_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_monadInfo_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutVars_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutVarDefs_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contInfo_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deadCode_5354_: u8 = 0;
    let mut v_ops_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5363_: u8 = 0;
    let mut v_unused_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_monadInfo_5350_ = lean_ctor_get(v___y_5342_, 0);
                v_mutVars_5351_ = lean_ctor_get(v___y_5342_, 1);
                v_mutVarDefs_5352_ = lean_ctor_get(v___y_5342_, 2);
                v_contInfo_5353_ = lean_ctor_get(v___y_5342_, 4);
                v_deadCode_5354_ = lean_ctor_get_uint8(
                    v___y_5342_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_ops_5355_ = lean_ctor_get(v___y_5342_, 5);
                v_isSharedCheck_5363_ = (!lean_is_exclusive(v___y_5342_)) as u8;
                if v_isSharedCheck_5363_ == 0 {
                    v_unused_5364_ = lean_ctor_get(v___y_5342_, 3);
                    lean_dec(v_unused_5364_);
                    v___x_5357_ = v___y_5342_;
                    v_isShared_5358_ = v_isSharedCheck_5363_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ops_5355_);
                    lean_inc(v_contInfo_5353_);
                    lean_inc(v_mutVarDefs_5352_);
                    lean_inc(v_mutVars_5351_);
                    lean_inc(v_monadInfo_5350_);
                    lean_dec(v___y_5342_);
                    v___x_5357_ = lean_box(0);
                    v_isShared_5358_ = v_isSharedCheck_5363_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5358_ == 0 {
                    lean_ctor_set(v___x_5357_, 3, v___x_5337_);
                    v___x_5360_ = v___x_5357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 6, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_monadInfo_5350_);
                    lean_ctor_set(v_reuseFailAlloc_5362_, 1, v_mutVars_5351_);
                    lean_ctor_set(v_reuseFailAlloc_5362_, 2, v_mutVarDefs_5352_);
                    lean_ctor_set(v_reuseFailAlloc_5362_, 3, v___x_5337_);
                    lean_ctor_set(v_reuseFailAlloc_5362_, 4, v_contInfo_5353_);
                    lean_ctor_set(v_reuseFailAlloc_5362_, 5, v_ops_5355_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5362_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
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
                lean_dec_ref(v___x_5360_);
                return v___x_5361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__7___boxed(
    mut v___x_5365_: *mut LeanObject,
    mut v___f_5366_: *mut LeanObject,
    mut v___f_5367_: *mut LeanObject,
    mut v___x_5368_: *mut LeanObject,
    mut v___x_5369_: *mut LeanObject,
    mut v___y_5370_: *mut LeanObject,
    mut v___y_5371_: *mut LeanObject,
    mut v___y_5372_: *mut LeanObject,
    mut v___y_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
    mut v___y_5375_: *mut LeanObject,
    mut v___y_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5378_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5376_);
    lean_dec_ref(v___y_5375_);
    lean_dec(v___y_5374_);
    lean_dec_ref(v___y_5373_);
    lean_dec(v___y_5372_);
    lean_dec_ref(v___y_5371_);
    return v_res_5378_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__8(
    mut v_a_5382_: *mut LeanObject,
    mut v_a_5383_: *mut LeanObject,
    mut v_u_5384_: *mut LeanObject,
    mut v_snd_5385_: *mut LeanObject,
    mut v___f_5386_: *mut LeanObject,
    mut v___x_5387_: *mut LeanObject,
    mut v_body_5388_: *mut LeanObject,
    mut v___x_5389_: u8,
    mut v___y_5390_: *mut LeanObject,
    mut v_xh_5391_: *mut LeanObject,
    mut v_loopS_5392_: *mut LeanObject,
    mut v___y_5393_: *mut LeanObject,
    mut v___y_5394_: *mut LeanObject,
    mut v___y_5395_: *mut LeanObject,
    mut v___y_5396_: *mut LeanObject,
    mut v___y_5397_: *mut LeanObject,
    mut v___y_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_resultType_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_resultName_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: u8 = 0;
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_unused_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_unused_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_resultType_5401_ = lean_ctor_get(v_a_5382_, 0);
                v_isSharedCheck_5438_ = (!lean_is_exclusive(v_a_5382_)) as u8;
                if v_isSharedCheck_5438_ == 0 {
                    v_unused_5439_ = lean_ctor_get(v_a_5382_, 1);
                    lean_dec(v_unused_5439_);
                    v___x_5403_ = v_a_5382_;
                    v_isShared_5404_ = v_isSharedCheck_5438_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_resultType_5401_);
                    lean_dec(v_a_5382_);
                    v___x_5403_ = lean_box(0);
                    v_isShared_5404_ = v_isSharedCheck_5438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_resultName_5405_ = lean_ctor_get(v_a_5383_, 0);
                v_resultType_5406_ = lean_ctor_get(v_a_5383_, 1);
                v_isSharedCheck_5436_ = (!lean_is_exclusive(v_a_5383_)) as u8;
                if v_isSharedCheck_5436_ == 0 {
                    v_unused_5437_ = lean_ctor_get(v_a_5383_, 2);
                    lean_dec(v_unused_5437_);
                    v___x_5408_ = v_a_5383_;
                    v_isShared_5409_ = v_isSharedCheck_5436_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_resultType_5406_);
                    lean_inc(v_resultName_5405_);
                    lean_dec(v_a_5383_);
                    v___x_5408_ = lean_box(0);
                    v_isShared_5409_ = v_isSharedCheck_5436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5410_ = l_Lean_Expr_fvarId_x21(v_loopS_5392_);
                v___x_5411_ = l_Lean_Elab_Do_elabDoFor___lam__8___closed__0;
                v___x_5412_ = l_Lean_Elab_Do_elabDoFor___lam__8___closed__1;
                v___x_5413_ = lean_box(0);
                lean_inc_n(v_u_5384_, 3);
                v___x_5414_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5414_, 0, v_u_5384_);
                lean_ctor_set(v___x_5414_, 1, v___x_5413_);
                lean_inc_ref_n(v___x_5414_, 3);
                v___x_5415_ = l_Lean_mkConst(v___x_5412_, v___x_5414_);
                lean_inc_ref_n(v_snd_5385_, 3);
                v___x_5416_ = l_Lean_Expr_app___override(v___x_5415_, v_snd_5385_);
                lean_inc_ref_n(v___x_5416_, 3);
                lean_inc_ref_n(v___f_5386_, 2);
                v___f_5417_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__4___boxed as *mut core::ffi::c_void,
                    15,
                    6,
                );
                lean_closure_set(v___f_5417_, 0, v___f_5386_);
                lean_closure_set(v___f_5417_, 1, v_u_5384_);
                lean_closure_set(v___f_5417_, 2, v___x_5411_);
                lean_closure_set(v___f_5417_, 3, v___x_5414_);
                lean_closure_set(v___f_5417_, 4, v_snd_5385_);
                lean_closure_set(v___f_5417_, 5, v___x_5416_);
                lean_inc(v___x_5387_);
                v___f_5418_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__5___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                lean_closure_set(v___f_5418_, 0, v___f_5386_);
                lean_closure_set(v___f_5418_, 1, v___x_5387_);
                lean_closure_set(v___f_5418_, 2, v_u_5384_);
                lean_closure_set(v___f_5418_, 3, v___x_5411_);
                lean_closure_set(v___f_5418_, 4, v___x_5414_);
                lean_closure_set(v___f_5418_, 5, v_snd_5385_);
                lean_closure_set(v___f_5418_, 6, v___x_5416_);
                v___f_5419_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__6___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                lean_closure_set(v___f_5419_, 0, v___f_5386_);
                lean_closure_set(v___f_5419_, 1, v___x_5387_);
                lean_closure_set(v___f_5419_, 2, v_u_5384_);
                lean_closure_set(v___f_5419_, 3, v___x_5411_);
                lean_closure_set(v___f_5419_, 4, v___x_5414_);
                lean_closure_set(v___f_5419_, 5, v_snd_5385_);
                lean_closure_set(v___f_5419_, 6, v___x_5416_);
                if v_isShared_5404_ == 0 {
                    lean_ctor_set(v___x_5403_, 1, v___f_5417_);
                    v___x_5421_ = v___x_5403_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_resultType_5401_);
                    lean_ctor_set(v_reuseFailAlloc_5435_, 1, v___f_5417_);
                    v___x_5421_ = v_reuseFailAlloc_5435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5422_ = 1;
                lean_inc_ref(v___f_5418_);
                if v_isShared_5409_ == 0 {
                    lean_ctor_set(v___x_5408_, 2, v___f_5418_);
                    v___x_5424_ = v___x_5408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_resultName_5405_);
                    lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_resultType_5406_);
                    lean_ctor_set(v_reuseFailAlloc_5434_, 2, v___f_5418_);
                    v___x_5424_ = v_reuseFailAlloc_5434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_5424_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5422_,
                );
                v___x_5425_ = lean_box((v___x_5389_) as usize);
                v___x_5426_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                lean_closure_set(v___x_5426_, 0, v_body_5388_);
                lean_closure_set(v___x_5426_, 1, v___x_5424_);
                lean_closure_set(v___x_5426_, 2, v___x_5425_);
                v___f_5427_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__7___boxed as *mut core::ffi::c_void,
                    13,
                    5,
                );
                lean_closure_set(v___f_5427_, 0, v___x_5416_);
                lean_closure_set(v___f_5427_, 1, v___f_5419_);
                lean_closure_set(v___f_5427_, 2, v___f_5418_);
                lean_closure_set(v___f_5427_, 3, v___x_5421_);
                lean_closure_set(v___f_5427_, 4, v___x_5426_);
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
                if lean_obj_tag(v___x_5428_) == 0 {
                    v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
                    lean_inc(v_a_5429_);
                    lean_dec_ref_known(v___x_5428_, 1);
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
                    lean_dec_ref(v___x_5430_);
                    return v___x_5433_;
                } else {
                    lean_dec_ref(v_loopS_5392_);
                    lean_dec_ref(v_xh_5391_);
                    return v___x_5428_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__8___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5440_: *mut LeanObject = *_args.add(0);
    let mut v_a_5441_: *mut LeanObject = *_args.add(1);
    let mut v_u_5442_: *mut LeanObject = *_args.add(2);
    let mut v_snd_5443_: *mut LeanObject = *_args.add(3);
    let mut v___f_5444_: *mut LeanObject = *_args.add(4);
    let mut v___x_5445_: *mut LeanObject = *_args.add(5);
    let mut v_body_5446_: *mut LeanObject = *_args.add(6);
    let mut v___x_5447_: *mut LeanObject = *_args.add(7);
    let mut v___y_5448_: *mut LeanObject = *_args.add(8);
    let mut v_xh_5449_: *mut LeanObject = *_args.add(9);
    let mut v_loopS_5450_: *mut LeanObject = *_args.add(10);
    let mut v___y_5451_: *mut LeanObject = *_args.add(11);
    let mut v___y_5452_: *mut LeanObject = *_args.add(12);
    let mut v___y_5453_: *mut LeanObject = *_args.add(13);
    let mut v___y_5454_: *mut LeanObject = *_args.add(14);
    let mut v___y_5455_: *mut LeanObject = *_args.add(15);
    let mut v___y_5456_: *mut LeanObject = *_args.add(16);
    let mut v___y_5457_: *mut LeanObject = *_args.add(17);
    let mut v___y_5458_: *mut LeanObject = *_args.add(18);
    let mut v___x_72062__boxed_5459_: u8 = 0;
    let mut v_res_5460_: *mut LeanObject = core::ptr::null_mut();
    v___x_72062__boxed_5459_ = (lean_unbox(v___x_5447_) as u8);
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
    lean_dec(v___y_5457_);
    lean_dec_ref(v___y_5456_);
    lean_dec(v___y_5455_);
    lean_dec_ref(v___y_5454_);
    lean_dec(v___y_5453_);
    lean_dec_ref(v___y_5452_);
    lean_dec_ref(v___y_5451_);
    return v_res_5460_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__9(
    mut v___x_5461_: *mut LeanObject,
    mut v___x_5462_: *mut LeanObject,
    mut v_x_5463_: *mut LeanObject,
    mut v_a_5464_: *mut LeanObject,
    mut v_a_5465_: *mut LeanObject,
    mut v_u_5466_: *mut LeanObject,
    mut v_snd_5467_: *mut LeanObject,
    mut v___f_5468_: *mut LeanObject,
    mut v___x_5469_: *mut LeanObject,
    mut v_body_5470_: *mut LeanObject,
    mut v___x_5471_: u8,
    mut v___y_5472_: *mut LeanObject,
    mut v_a_5473_: *mut LeanObject,
    mut v_h_x3f_5474_: *mut LeanObject,
    mut v___x_5475_: *mut LeanObject,
    mut v_xh_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: u8 = 0;
    let mut v___x_5498_: u8 = 0;
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5506_: u8 = 0;
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5510_: u8 = 0;
    let mut v_a_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5485_ = lean_array_get_borrowed(v___x_5461_, v_xh_5476_, v___x_5462_);
                lean_inc(v___x_5485_);
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
                if lean_obj_tag(v___x_5486_) == 0 {
                    lean_dec_ref_known(v___x_5486_, 1);
                    v___x_5487_ = lean_box((v___x_5471_) as usize);
                    lean_inc_ref(v_xh_5476_);
                    lean_inc_ref(v_snd_5467_);
                    v___f_5488_ = lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__8___boxed as *mut core::ffi::c_void,
                        19,
                        10,
                    );
                    lean_closure_set(v___f_5488_, 0, v_a_5464_);
                    lean_closure_set(v___f_5488_, 1, v_a_5465_);
                    lean_closure_set(v___f_5488_, 2, v_u_5466_);
                    lean_closure_set(v___f_5488_, 3, v_snd_5467_);
                    lean_closure_set(v___f_5488_, 4, v___f_5468_);
                    lean_closure_set(v___f_5488_, 5, v___x_5469_);
                    lean_closure_set(v___f_5488_, 6, v_body_5470_);
                    lean_closure_set(v___f_5488_, 7, v___x_5487_);
                    lean_closure_set(v___f_5488_, 8, v___y_5472_);
                    lean_closure_set(v___f_5488_, 9, v_xh_5476_);
                    if lean_obj_tag(v_h_x3f_5474_) == 1 {
                        v_val_5500_ = lean_ctor_get(v_h_x3f_5474_, 0);
                        lean_inc(v_val_5500_);
                        lean_dec_ref_known(v_h_x3f_5474_, 1);
                        v___x_5501_ = lean_array_get(v___x_5461_, v_xh_5476_, v___x_5475_);
                        lean_dec_ref(v_xh_5476_);
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
                        if lean_obj_tag(v___x_5502_) == 0 {
                            lean_dec_ref_known(v___x_5502_, 1);
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
                            lean_dec_ref(v___f_5488_);
                            lean_dec(v_a_5473_);
                            lean_dec_ref(v_snd_5467_);
                            v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
                            v_isSharedCheck_5510_ = (!lean_is_exclusive(v___x_5502_)) as u8;
                            if v_isSharedCheck_5510_ == 0 {
                                v___x_5505_ = v___x_5502_;
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_5503_);
                                lean_dec(v___x_5502_);
                                v___x_5505_ = lean_box(0);
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_xh_5476_);
                        lean_dec(v_h_x3f_5474_);
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
                    lean_dec_ref(v_xh_5476_);
                    lean_dec(v_h_x3f_5474_);
                    lean_dec(v_a_5473_);
                    lean_dec(v___y_5472_);
                    lean_dec(v_body_5470_);
                    lean_dec(v___x_5469_);
                    lean_dec_ref(v___f_5468_);
                    lean_dec_ref(v_snd_5467_);
                    lean_dec(v_u_5466_);
                    lean_dec_ref(v_a_5465_);
                    lean_dec_ref(v_a_5464_);
                    v_a_5511_ = lean_ctor_get(v___x_5486_, 0);
                    v_isSharedCheck_5518_ = (!lean_is_exclusive(v___x_5486_)) as u8;
                    if v_isSharedCheck_5518_ == 0 {
                        v___x_5513_ = v___x_5486_;
                        v_isShared_5514_ = v_isSharedCheck_5518_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5511_);
                        lean_dec(v___x_5486_);
                        v___x_5513_ = lean_box(0);
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
                    v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
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
                    v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5519_: *mut LeanObject = *_args.add(0);
    let mut v___x_5520_: *mut LeanObject = *_args.add(1);
    let mut v_x_5521_: *mut LeanObject = *_args.add(2);
    let mut v_a_5522_: *mut LeanObject = *_args.add(3);
    let mut v_a_5523_: *mut LeanObject = *_args.add(4);
    let mut v_u_5524_: *mut LeanObject = *_args.add(5);
    let mut v_snd_5525_: *mut LeanObject = *_args.add(6);
    let mut v___f_5526_: *mut LeanObject = *_args.add(7);
    let mut v___x_5527_: *mut LeanObject = *_args.add(8);
    let mut v_body_5528_: *mut LeanObject = *_args.add(9);
    let mut v___x_5529_: *mut LeanObject = *_args.add(10);
    let mut v___y_5530_: *mut LeanObject = *_args.add(11);
    let mut v_a_5531_: *mut LeanObject = *_args.add(12);
    let mut v_h_x3f_5532_: *mut LeanObject = *_args.add(13);
    let mut v___x_5533_: *mut LeanObject = *_args.add(14);
    let mut v_xh_5534_: *mut LeanObject = *_args.add(15);
    let mut v___y_5535_: *mut LeanObject = *_args.add(16);
    let mut v___y_5536_: *mut LeanObject = *_args.add(17);
    let mut v___y_5537_: *mut LeanObject = *_args.add(18);
    let mut v___y_5538_: *mut LeanObject = *_args.add(19);
    let mut v___y_5539_: *mut LeanObject = *_args.add(20);
    let mut v___y_5540_: *mut LeanObject = *_args.add(21);
    let mut v___y_5541_: *mut LeanObject = *_args.add(22);
    let mut v___y_5542_: *mut LeanObject = *_args.add(23);
    let mut v___x_72185__boxed_5543_: u8 = 0;
    let mut v_res_5544_: *mut LeanObject = core::ptr::null_mut();
    v___x_72185__boxed_5543_ = (lean_unbox(v___x_5529_) as u8);
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
    lean_dec(v___y_5541_);
    lean_dec_ref(v___y_5540_);
    lean_dec(v___y_5539_);
    lean_dec_ref(v___y_5538_);
    lean_dec(v___y_5537_);
    lean_dec_ref(v___y_5536_);
    lean_dec_ref(v___y_5535_);
    lean_dec(v___x_5533_);
    lean_dec(v___x_5520_);
    lean_dec_ref(v___x_5519_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
    mut v_name_5545_: *mut LeanObject,
    mut v_type_5546_: *mut LeanObject,
    mut v_k_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
    mut v___y_5552_: *mut LeanObject,
    mut v___y_5553_: *mut LeanObject,
    mut v___y_5554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5556_: u8 = 0;
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_name_5559_: *mut LeanObject,
    mut v_type_5560_: *mut LeanObject,
    mut v_k_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
    mut v___y_5564_: *mut LeanObject,
    mut v___y_5565_: *mut LeanObject,
    mut v___y_5566_: *mut LeanObject,
    mut v___y_5567_: *mut LeanObject,
    mut v___y_5568_: *mut LeanObject,
    mut v___y_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5570_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5568_);
    lean_dec_ref(v___y_5567_);
    lean_dec(v___y_5566_);
    lean_dec_ref(v___y_5565_);
    lean_dec(v___y_5564_);
    lean_dec_ref(v___y_5563_);
    lean_dec_ref(v___y_5562_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__10(
    mut v_returnsEarly_5588_: u8,
    mut v_a_5589_: *mut LeanObject,
    mut v_a_5590_: *mut LeanObject,
    mut v_doBlockResultType_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
    mut v_v_5593_: *mut LeanObject,
    mut v_u_5594_: *mut LeanObject,
    mut v___f_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___x_5597_: *mut LeanObject,
    mut v___x_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
    mut v___y_5600_: *mut LeanObject,
    mut v___y_5601_: *mut LeanObject,
    mut v___y_5602_: *mut LeanObject,
    mut v___y_5603_: *mut LeanObject,
    mut v___y_5604_: *mut LeanObject,
    mut v___y_5605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ret_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: u8 = 0;
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_reuseFailAlloc_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_unused_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_returnsEarly_5588_ == 0 {
                    lean_dec_ref(v___f_5595_);
                    lean_dec(v_u_5594_);
                    lean_dec(v_v_5593_);
                    lean_dec_ref(v_a_5592_);
                    lean_dec_ref(v_doBlockResultType_5591_);
                    lean_dec(v_a_5590_);
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
                    if lean_obj_tag(v___x_5663_) == 0 {
                        v_a_5664_ = lean_ctor_get(v___x_5663_, 0);
                        lean_inc(v_a_5664_);
                        lean_dec_ref_known(v___x_5663_, 1);
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
                            if lean_obj_tag(v___x_5670_) == 0 {
                                v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
                                lean_inc(v_a_5671_);
                                lean_dec_ref_known(v___x_5670_, 1);
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
                                lean_dec_ref(v___f_5595_);
                                lean_dec(v_u_5594_);
                                lean_dec(v_v_5593_);
                                lean_dec_ref(v_a_5592_);
                                lean_dec_ref(v_doBlockResultType_5591_);
                                lean_dec_ref(v_a_5589_);
                                return v___x_5670_;
                            }
                        }
                    } else {
                        lean_dec_ref(v___f_5595_);
                        lean_dec(v_u_5594_);
                        lean_dec(v_v_5593_);
                        lean_dec_ref(v_a_5592_);
                        lean_dec_ref(v_doBlockResultType_5591_);
                        lean_dec_ref(v_a_5589_);
                        return v___x_5663_;
                    }
                }
            }
            1 => {
                lean_inc(v___y_5615_);
                lean_inc_ref(v___y_5614_);
                lean_inc(v___y_5613_);
                lean_inc_ref(v___y_5612_);
                lean_inc_ref(v_ret_5608_);
                v___x_5616_ = lean_infer_type(
                    v_ret_5608_,
                    v___y_5612_,
                    v___y_5613_,
                    v___y_5614_,
                    v___y_5615_,
                );
                if lean_obj_tag(v___x_5616_) == 0 {
                    v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
                    lean_inc(v_a_5617_);
                    lean_dec_ref_known(v___x_5616_, 1);
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
                    if lean_obj_tag(v___x_5618_) == 0 {
                        v_a_5619_ = lean_ctor_get(v___x_5618_, 0);
                        lean_inc(v_a_5619_);
                        lean_dec_ref_known(v___x_5618_, 1);
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
                        if lean_obj_tag(v___x_5620_) == 0 {
                            v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
                            lean_inc(v_a_5621_);
                            lean_dec_ref_known(v___x_5620_, 1);
                            v___x_5622_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__1;
                            v___x_5623_ =
                                l_Lean_Core_mkFreshUserName(v___x_5622_, v___y_5614_, v___y_5615_);
                            if lean_obj_tag(v___x_5623_) == 0 {
                                v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
                                lean_inc(v_a_5624_);
                                lean_dec_ref_known(v___x_5623_, 1);
                                v_resultType_5625_ = lean_ctor_get(v_a_5592_, 0);
                                v_isSharedCheck_5652_ = (!lean_is_exclusive(v_a_5592_)) as u8;
                                if v_isSharedCheck_5652_ == 0 {
                                    v_unused_5653_ = lean_ctor_get(v_a_5592_, 1);
                                    lean_dec(v_unused_5653_);
                                    v___x_5627_ = v_a_5592_;
                                    v_isShared_5628_ = v_isSharedCheck_5652_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_resultType_5625_);
                                    lean_dec(v_a_5592_);
                                    v___x_5627_ = lean_box(0);
                                    v_isShared_5628_ = v_isSharedCheck_5652_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5621_);
                                lean_dec(v_a_5619_);
                                lean_dec(v_a_5617_);
                                lean_dec_ref(v_ret_5608_);
                                lean_dec_ref(v___f_5595_);
                                lean_dec(v_u_5594_);
                                lean_dec(v_v_5593_);
                                lean_dec_ref(v_a_5592_);
                                v_a_5654_ = lean_ctor_get(v___x_5623_, 0);
                                v_isSharedCheck_5661_ = (!lean_is_exclusive(v___x_5623_)) as u8;
                                if v_isSharedCheck_5661_ == 0 {
                                    v___x_5656_ = v___x_5623_;
                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5654_);
                                    lean_dec(v___x_5623_);
                                    v___x_5656_ = lean_box(0);
                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5619_);
                            lean_dec(v_a_5617_);
                            lean_dec_ref(v_ret_5608_);
                            lean_dec_ref(v___f_5595_);
                            lean_dec(v_u_5594_);
                            lean_dec(v_v_5593_);
                            lean_dec_ref(v_a_5592_);
                            return v___x_5620_;
                        }
                    } else {
                        lean_dec(v_a_5617_);
                        lean_dec_ref(v_ret_5608_);
                        lean_dec_ref(v___f_5595_);
                        lean_dec(v_u_5594_);
                        lean_dec(v_v_5593_);
                        lean_dec_ref(v_a_5592_);
                        lean_dec_ref(v_a_5589_);
                        return v___x_5618_;
                    }
                } else {
                    lean_dec_ref(v_ret_5608_);
                    lean_dec_ref(v___f_5595_);
                    lean_dec(v_u_5594_);
                    lean_dec(v_v_5593_);
                    lean_dec_ref(v_a_5592_);
                    lean_dec_ref(v_doBlockResultType_5591_);
                    lean_dec_ref(v_a_5589_);
                    return v___x_5616_;
                }
            }
            2 => {
                v___x_5629_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__2;
                v___x_5630_ = 0;
                v___x_5631_ = l_Lean_mkLambda(v___x_5629_, v___x_5630_, v_a_5617_, v_a_5619_);
                v___x_5632_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__6;
                v___x_5633_ = l_Lean_Level_succ___override(v_v_5593_);
                v___x_5634_ = lean_box(0);
                if v_isShared_5628_ == 0 {
                    lean_ctor_set_tag(v___x_5627_, 1);
                    lean_ctor_set(v___x_5627_, 1, v___x_5634_);
                    lean_ctor_set(v___x_5627_, 0, v___x_5633_);
                    v___x_5636_ = v___x_5627_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5633_);
                    lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___x_5634_);
                    v___x_5636_ = v_reuseFailAlloc_5651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5637_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5637_, 0, v_u_5594_);
                lean_ctor_set(v___x_5637_, 1, v___x_5636_);
                v___x_5638_ = l_Lean_mkConst(v___x_5632_, v___x_5637_);
                lean_inc_ref(v_resultType_5625_);
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
                if lean_obj_tag(v___x_5640_) == 0 {
                    v_a_5641_ = lean_ctor_get(v___x_5640_, 0);
                    v_isSharedCheck_5650_ = (!lean_is_exclusive(v___x_5640_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v___x_5643_ = v___x_5640_;
                        v_isShared_5644_ = v_isSharedCheck_5650_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5641_);
                        lean_dec(v___x_5640_);
                        v___x_5643_ = lean_box(0);
                        v_isShared_5644_ = v_isSharedCheck_5650_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5639_);
                    lean_dec(v_a_5621_);
                    return v___x_5640_;
                }
            }
            4 => {
                v___x_5645_ = l_Lean_mkSimpleThunk(v_a_5621_);
                v___x_5646_ = l_Lean_mkAppB(v___x_5639_, v_a_5641_, v___x_5645_);
                if v_isShared_5644_ == 0 {
                    lean_ctor_set(v___x_5643_, 0, v___x_5646_);
                    v___x_5648_ = v___x_5643_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
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
                    v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_returnsEarly_5672_: *mut LeanObject = *_args.add(0);
    let mut v_a_5673_: *mut LeanObject = *_args.add(1);
    let mut v_a_5674_: *mut LeanObject = *_args.add(2);
    let mut v_doBlockResultType_5675_: *mut LeanObject = *_args.add(3);
    let mut v_a_5676_: *mut LeanObject = *_args.add(4);
    let mut v_v_5677_: *mut LeanObject = *_args.add(5);
    let mut v_u_5678_: *mut LeanObject = *_args.add(6);
    let mut v___f_5679_: *mut LeanObject = *_args.add(7);
    let mut v___y_5680_: *mut LeanObject = *_args.add(8);
    let mut v___x_5681_: *mut LeanObject = *_args.add(9);
    let mut v___x_5682_: *mut LeanObject = *_args.add(10);
    let mut v___y_5683_: *mut LeanObject = *_args.add(11);
    let mut v___y_5684_: *mut LeanObject = *_args.add(12);
    let mut v___y_5685_: *mut LeanObject = *_args.add(13);
    let mut v___y_5686_: *mut LeanObject = *_args.add(14);
    let mut v___y_5687_: *mut LeanObject = *_args.add(15);
    let mut v___y_5688_: *mut LeanObject = *_args.add(16);
    let mut v___y_5689_: *mut LeanObject = *_args.add(17);
    let mut v___y_5690_: *mut LeanObject = *_args.add(18);
    let mut v_returnsEarly_boxed_5691_: u8 = 0;
    let mut v_res_5692_: *mut LeanObject = core::ptr::null_mut();
    v_returnsEarly_boxed_5691_ = (lean_unbox(v_returnsEarly_5672_) as u8);
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
    lean_dec(v___y_5689_);
    lean_dec_ref(v___y_5688_);
    lean_dec(v___y_5687_);
    lean_dec_ref(v___y_5686_);
    lean_dec(v___y_5685_);
    lean_dec_ref(v___y_5684_);
    lean_dec_ref(v___y_5683_);
    lean_dec(v___x_5682_);
    lean_dec(v___x_5681_);
    lean_dec_ref(v___y_5680_);
    return v_res_5692_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__11(
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___x_5695_: *mut LeanObject,
    mut v___x_5696_: u8,
    mut v_postS_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
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
    if lean_obj_tag(v___x_5707_) == 0 {
        let mut v_a_5708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5711_: u8 = 0;
        let mut v___x_5712_: u8 = 0;
        let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
        v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
        lean_inc(v_a_5708_);
        lean_dec_ref_known(v___x_5707_, 1);
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
        lean_dec_ref(v___x_5710_);
        return v___x_5713_;
    } else {
        lean_dec_ref(v_postS_5697_);
        return v___x_5707_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__11___boxed(
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
    mut v___x_5716_: *mut LeanObject,
    mut v___x_5717_: *mut LeanObject,
    mut v_postS_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_72567__boxed_5727_: u8 = 0;
    let mut v_res_5728_: *mut LeanObject = core::ptr::null_mut();
    v___x_72567__boxed_5727_ = (lean_unbox(v___x_5717_) as u8);
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
    lean_dec(v___y_5725_);
    lean_dec_ref(v___y_5724_);
    lean_dec(v___y_5723_);
    lean_dec_ref(v___y_5722_);
    lean_dec(v___y_5721_);
    lean_dec_ref(v___y_5720_);
    lean_dec_ref(v___y_5719_);
    lean_dec(v___x_5716_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__12(
    mut v_a_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
    mut v___x_5736_: *mut LeanObject,
    mut v_a_5737_: *mut LeanObject,
    mut v_a_5738_: *mut LeanObject,
    mut v_val_5739_: *mut LeanObject,
    mut v_a_5740_: *mut LeanObject,
    mut v_x_5741_: *mut LeanObject,
    mut v___y_5742_: *mut LeanObject,
    mut v___y_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_Elab_Do_elabDoFor___lam__12___closed__2;
    v___x_5751_ = lean_box(0);
    v___x_5752_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5752_, 0, v_a_5734_);
    lean_ctor_set(v___x_5752_, 1, v___x_5751_);
    v___x_5753_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5753_, 0, v_a_5735_);
    lean_ctor_set(v___x_5753_, 1, v___x_5752_);
    v___x_5754_ = l_Lean_mkConst(v___x_5750_, v___x_5753_);
    v___x_5755_ = l_Lean_instInhabitedExpr;
    v___x_5756_ = lean_array_get_borrowed(v___x_5755_, v_x_5741_, v___x_5736_);
    lean_inc(v___x_5756_);
    v___x_5757_ = l_Lean_mkApp5(
        v___x_5754_,
        v_a_5737_,
        v_a_5738_,
        v_val_5739_,
        v_a_5740_,
        v___x_5756_,
    );
    v___x_5758_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__12___boxed(
    mut v_a_5759_: *mut LeanObject,
    mut v_a_5760_: *mut LeanObject,
    mut v___x_5761_: *mut LeanObject,
    mut v_a_5762_: *mut LeanObject,
    mut v_a_5763_: *mut LeanObject,
    mut v_val_5764_: *mut LeanObject,
    mut v_a_5765_: *mut LeanObject,
    mut v_x_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5775_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5773_);
    lean_dec_ref(v___y_5772_);
    lean_dec(v___y_5771_);
    lean_dec_ref(v___y_5770_);
    lean_dec(v___y_5769_);
    lean_dec_ref(v___y_5768_);
    lean_dec_ref(v___y_5767_);
    lean_dec_ref(v_x_5766_);
    lean_dec(v___x_5761_);
    return v_res_5775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(
    mut v_a_5776_: *mut LeanObject,
    mut v_as_5777_: *mut LeanObject,
    mut v_i_5778_: usize,
    mut v_stop_5779_: usize,
    mut v_b_5780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5786_: u8 = 0;
    let mut v_reassigns_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5786_ = lean_usize_dec_eq(v_i_5778_, v_stop_5779_);
                if v___x_5786_ == 0 {
                    v_reassigns_5787_ = lean_ctor_get(v_a_5776_, 1);
                    v___x_5788_ = lean_array_uget_borrowed(v_as_5777_, v_i_5778_);
                    v___x_5789_ = l_Lean_TSyntax_getId(v___x_5788_);
                    v___x_5790_ = l_Lean_NameSet_contains(v_reassigns_5787_, v___x_5789_);
                    lean_dec(v___x_5789_);
                    if v___x_5790_ == 0 {
                        v___y_5782_ = v_b_5780_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_5788_);
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
    mut v_a_5792_: *mut LeanObject,
    mut v_as_5793_: *mut LeanObject,
    mut v_i_5794_: *mut LeanObject,
    mut v_stop_5795_: *mut LeanObject,
    mut v_b_5796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5797_: usize = 0;
    let mut v_stop_boxed_5798_: usize = 0;
    let mut v_res_5799_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5797_ = lean_unbox_usize(v_i_5794_);
    lean_dec(v_i_5794_);
    v_stop_boxed_5798_ = lean_unbox_usize(v_stop_5795_);
    lean_dec(v_stop_5795_);
    v_res_5799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_5792_, v_as_5793_, v_i_boxed_5797_, v_stop_boxed_5798_, v_b_5796_);
    lean_dec_ref(v_as_5793_);
    lean_dec_ref(v_a_5792_);
    return v_res_5799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(
    mut v_sz_5800_: usize,
    mut v_i_5801_: usize,
    mut v_bs_5802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5803_: u8 = 0;
    let mut v_v_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: usize = 0;
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5803_ = lean_usize_dec_lt(v_i_5801_, v_sz_5800_);
                if v___x_5803_ == 0 {
                    return v_bs_5802_;
                } else {
                    v_v_5804_ = lean_array_uget(v_bs_5802_, v_i_5801_);
                    v___x_5805_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5806_ = lean_array_uset(v_bs_5802_, v_i_5801_, v___x_5805_);
                    v___x_5807_ = l_Lean_TSyntax_getId(v_v_5804_);
                    lean_dec(v_v_5804_);
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
    mut v_sz_5812_: *mut LeanObject,
    mut v_i_5813_: *mut LeanObject,
    mut v_bs_5814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5815_: usize = 0;
    let mut v_i_boxed_5816_: usize = 0;
    let mut v_res_5817_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5815_ = lean_unbox_usize(v_sz_5812_);
    lean_dec(v_sz_5812_);
    v_i_boxed_5816_ = lean_unbox_usize(v_i_5813_);
    lean_dec(v_i_5813_);
    v_res_5817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_boxed_5815_, v_i_boxed_5816_, v_bs_5814_);
    return v_res_5817_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(
    mut v___x_5818_: *mut LeanObject,
    mut v_a_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_70870__overap_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_instInhabitedExpr;
    v___x_70870__overap_5829_ = l_instInhabitedOfMonad___redArg(v___x_5818_, v___x_5828_);
    lean_inc(v___y_5826_);
    lean_inc_ref(v___y_5825_);
    lean_inc(v___y_5824_);
    lean_inc_ref(v___y_5823_);
    lean_inc(v___y_5822_);
    lean_inc_ref(v___y_5821_);
    lean_inc_ref(v___y_5820_);
    v___x_5830_ = lean_apply_8(
        v___x_70870__overap_5829_,
        v___y_5820_,
        v___y_5821_,
        v___y_5822_,
        v___y_5823_,
        v___y_5824_,
        v___y_5825_,
        v___y_5826_,
        lean_box(0),
    );
    return v___x_5830_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(
    mut v___x_5831_: *mut LeanObject,
    mut v_a_5832_: *mut LeanObject,
    mut v___y_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5841_: *mut LeanObject = core::ptr::null_mut();
    v_res_5841_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_5831_, v_a_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
    lean_dec(v___y_5839_);
    lean_dec_ref(v___y_5838_);
    lean_dec(v___y_5837_);
    lean_dec_ref(v___y_5836_);
    lean_dec(v___y_5835_);
    lean_dec_ref(v___y_5834_);
    lean_dec_ref(v___y_5833_);
    lean_dec_ref(v_a_5832_);
    return v_res_5841_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0()
-> *mut LeanObject {
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    v___x_5842_ = l_instMonadEIO(lean_box(0));
    return v___x_5842_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1()
-> *mut LeanObject {
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    v___x_5843_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
    v___x_5844_ = l_StateRefT_x27_instMonad___redArg(v___x_5843_);
    return v___x_5844_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(
    mut v_acc_5851_: *mut LeanObject,
    mut v_declInfos_5852_: *mut LeanObject,
    mut v_k_5853_: *mut LeanObject,
    mut v_kind_5854_: *mut LeanObject,
    mut v_x_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
    mut v___y_5858_: *mut LeanObject,
    mut v___y_5859_: *mut LeanObject,
    mut v___y_5860_: *mut LeanObject,
    mut v___y_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_5864_: u8 = 0;
    let mut v_res_5865_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_5864_ = (lean_unbox(v_kind_5854_) as u8);
    v_res_5865_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_5851_, v_declInfos_5852_, v_k_5853_, v_kind_boxed_5864_, v_x_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
    lean_dec(v___y_5862_);
    lean_dec_ref(v___y_5861_);
    lean_dec(v___y_5860_);
    lean_dec_ref(v___y_5859_);
    lean_dec(v___y_5858_);
    lean_dec_ref(v___y_5857_);
    lean_dec_ref(v___y_5856_);
    return v_res_5865_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(
    mut v_declInfos_5866_: *mut LeanObject,
    mut v_k_5867_: *mut LeanObject,
    mut v_kind_5868_: u8,
    mut v_acc_5869_: *mut LeanObject,
    mut v___y_5870_: *mut LeanObject,
    mut v___y_5871_: *mut LeanObject,
    mut v___y_5872_: *mut LeanObject,
    mut v___y_5873_: *mut LeanObject,
    mut v___y_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v_toFunctor_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___f_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v_toFunctor_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5929_: u8 = 0;
    let mut v___f_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: u8 = 0;
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___f_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut v_unused_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5969_: u8 = 0;
    let mut v_unused_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_unused_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_unused_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5878_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
                v_toApplicative_5879_ = lean_ctor_get(v___x_5878_, 0);
                v_toFunctor_5880_ = lean_ctor_get(v_toApplicative_5879_, 0);
                v_toSeq_5881_ = lean_ctor_get(v_toApplicative_5879_, 2);
                v_toSeqLeft_5882_ = lean_ctor_get(v_toApplicative_5879_, 3);
                v_toSeqRight_5883_ = lean_ctor_get(v_toApplicative_5879_, 4);
                v___f_5884_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2;
                v___f_5885_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3;
                lean_inc_ref_n(v_toFunctor_5880_, 2);
                v___f_5886_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5886_, 0, v_toFunctor_5880_);
                v___f_5887_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5887_, 0, v_toFunctor_5880_);
                v___x_5888_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5888_, 0, v___f_5886_);
                lean_ctor_set(v___x_5888_, 1, v___f_5887_);
                lean_inc(v_toSeqRight_5883_);
                v___f_5889_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5889_, 0, v_toSeqRight_5883_);
                lean_inc(v_toSeqLeft_5882_);
                v___f_5890_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5890_, 0, v_toSeqLeft_5882_);
                lean_inc(v_toSeq_5881_);
                v___f_5891_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5891_, 0, v_toSeq_5881_);
                v___x_5892_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5892_, 0, v___x_5888_);
                lean_ctor_set(v___x_5892_, 1, v___f_5884_);
                lean_ctor_set(v___x_5892_, 2, v___f_5891_);
                lean_ctor_set(v___x_5892_, 3, v___f_5890_);
                lean_ctor_set(v___x_5892_, 4, v___f_5889_);
                v___x_5893_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5893_, 0, v___x_5892_);
                lean_ctor_set(v___x_5893_, 1, v___f_5885_);
                v___x_5894_ = l_StateRefT_x27_instMonad___redArg(v___x_5893_);
                v_toApplicative_5895_ = lean_ctor_get(v___x_5894_, 0);
                v_isSharedCheck_5975_ = (!lean_is_exclusive(v___x_5894_)) as u8;
                if v_isSharedCheck_5975_ == 0 {
                    v_unused_5976_ = lean_ctor_get(v___x_5894_, 1);
                    lean_dec(v_unused_5976_);
                    v___x_5897_ = v___x_5894_;
                    v_isShared_5898_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5895_);
                    lean_dec(v___x_5894_);
                    v___x_5897_ = lean_box(0);
                    v_isShared_5898_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5899_ = lean_ctor_get(v_toApplicative_5895_, 0);
                v_toSeq_5900_ = lean_ctor_get(v_toApplicative_5895_, 2);
                v_toSeqLeft_5901_ = lean_ctor_get(v_toApplicative_5895_, 3);
                v_toSeqRight_5902_ = lean_ctor_get(v_toApplicative_5895_, 4);
                v_isSharedCheck_5973_ = (!lean_is_exclusive(v_toApplicative_5895_)) as u8;
                if v_isSharedCheck_5973_ == 0 {
                    v_unused_5974_ = lean_ctor_get(v_toApplicative_5895_, 1);
                    lean_dec(v_unused_5974_);
                    v___x_5904_ = v_toApplicative_5895_;
                    v_isShared_5905_ = v_isSharedCheck_5973_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5902_);
                    lean_inc(v_toSeqLeft_5901_);
                    lean_inc(v_toSeq_5900_);
                    lean_inc(v_toFunctor_5899_);
                    lean_dec(v_toApplicative_5895_);
                    v___x_5904_ = lean_box(0);
                    v_isShared_5905_ = v_isSharedCheck_5973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4;
                v___f_5907_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5;
                lean_inc_ref(v_toFunctor_5899_);
                v___f_5908_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5908_, 0, v_toFunctor_5899_);
                v___f_5909_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5909_, 0, v_toFunctor_5899_);
                v___x_5910_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5910_, 0, v___f_5908_);
                lean_ctor_set(v___x_5910_, 1, v___f_5909_);
                v___f_5911_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5911_, 0, v_toSeqRight_5902_);
                v___f_5912_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5912_, 0, v_toSeqLeft_5901_);
                v___f_5913_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5913_, 0, v_toSeq_5900_);
                if v_isShared_5905_ == 0 {
                    lean_ctor_set(v___x_5904_, 4, v___f_5911_);
                    lean_ctor_set(v___x_5904_, 3, v___f_5912_);
                    lean_ctor_set(v___x_5904_, 2, v___f_5913_);
                    lean_ctor_set(v___x_5904_, 1, v___f_5906_);
                    lean_ctor_set(v___x_5904_, 0, v___x_5910_);
                    v___x_5915_ = v___x_5904_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5910_);
                    lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___f_5906_);
                    lean_ctor_set(v_reuseFailAlloc_5972_, 2, v___f_5913_);
                    lean_ctor_set(v_reuseFailAlloc_5972_, 3, v___f_5912_);
                    lean_ctor_set(v_reuseFailAlloc_5972_, 4, v___f_5911_);
                    v___x_5915_ = v_reuseFailAlloc_5972_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5898_ == 0 {
                    lean_ctor_set(v___x_5897_, 1, v___f_5907_);
                    lean_ctor_set(v___x_5897_, 0, v___x_5915_);
                    v___x_5917_ = v___x_5897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5915_);
                    lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___f_5907_);
                    v___x_5917_ = v_reuseFailAlloc_5971_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5918_ = l_StateRefT_x27_instMonad___redArg(v___x_5917_);
                v_toApplicative_5919_ = lean_ctor_get(v___x_5918_, 0);
                v_isSharedCheck_5969_ = (!lean_is_exclusive(v___x_5918_)) as u8;
                if v_isSharedCheck_5969_ == 0 {
                    v_unused_5970_ = lean_ctor_get(v___x_5918_, 1);
                    lean_dec(v_unused_5970_);
                    v___x_5921_ = v___x_5918_;
                    v_isShared_5922_ = v_isSharedCheck_5969_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5919_);
                    lean_dec(v___x_5918_);
                    v___x_5921_ = lean_box(0);
                    v_isShared_5922_ = v_isSharedCheck_5969_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5923_ = lean_ctor_get(v_toApplicative_5919_, 0);
                v_toSeq_5924_ = lean_ctor_get(v_toApplicative_5919_, 2);
                v_toSeqLeft_5925_ = lean_ctor_get(v_toApplicative_5919_, 3);
                v_toSeqRight_5926_ = lean_ctor_get(v_toApplicative_5919_, 4);
                v_isSharedCheck_5967_ = (!lean_is_exclusive(v_toApplicative_5919_)) as u8;
                if v_isSharedCheck_5967_ == 0 {
                    v_unused_5968_ = lean_ctor_get(v_toApplicative_5919_, 1);
                    lean_dec(v_unused_5968_);
                    v___x_5928_ = v_toApplicative_5919_;
                    v_isShared_5929_ = v_isSharedCheck_5967_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5926_);
                    lean_inc(v_toSeqLeft_5925_);
                    lean_inc(v_toSeq_5924_);
                    lean_inc(v_toFunctor_5923_);
                    lean_dec(v_toApplicative_5919_);
                    v___x_5928_ = lean_box(0);
                    v_isShared_5929_ = v_isSharedCheck_5967_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6;
                v___f_5931_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7;
                lean_inc_ref(v_toFunctor_5923_);
                v___f_5932_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5932_, 0, v_toFunctor_5923_);
                v___f_5933_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5933_, 0, v_toFunctor_5923_);
                v___x_5934_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5934_, 0, v___f_5932_);
                lean_ctor_set(v___x_5934_, 1, v___f_5933_);
                v___f_5935_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5935_, 0, v_toSeqRight_5926_);
                v___f_5936_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5936_, 0, v_toSeqLeft_5925_);
                v___f_5937_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5937_, 0, v_toSeq_5924_);
                if v_isShared_5929_ == 0 {
                    lean_ctor_set(v___x_5928_, 4, v___f_5935_);
                    lean_ctor_set(v___x_5928_, 3, v___f_5936_);
                    lean_ctor_set(v___x_5928_, 2, v___f_5937_);
                    lean_ctor_set(v___x_5928_, 1, v___f_5930_);
                    lean_ctor_set(v___x_5928_, 0, v___x_5934_);
                    v___x_5939_ = v___x_5928_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5934_);
                    lean_ctor_set(v_reuseFailAlloc_5966_, 1, v___f_5930_);
                    lean_ctor_set(v_reuseFailAlloc_5966_, 2, v___f_5937_);
                    lean_ctor_set(v_reuseFailAlloc_5966_, 3, v___f_5936_);
                    lean_ctor_set(v_reuseFailAlloc_5966_, 4, v___f_5935_);
                    v___x_5939_ = v_reuseFailAlloc_5966_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 1, v___f_5931_);
                    lean_ctor_set(v___x_5921_, 0, v___x_5939_);
                    v___x_5941_ = v___x_5921_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5965_, 0, v___x_5939_);
                    lean_ctor_set(v_reuseFailAlloc_5965_, 1, v___f_5931_);
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
                    lean_dec_ref(v___x_5942_);
                    lean_dec_ref(v_declInfos_5866_);
                    lean_inc(v___y_5876_);
                    lean_inc_ref(v___y_5875_);
                    lean_inc(v___y_5874_);
                    lean_inc_ref(v___y_5873_);
                    lean_inc(v___y_5872_);
                    lean_inc_ref(v___y_5871_);
                    lean_inc_ref(v___y_5870_);
                    v___x_5946_ = lean_apply_9(
                        v_k_5867_,
                        v_acc_5869_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                        v___y_5874_,
                        v___y_5875_,
                        v___y_5876_,
                        lean_box(0),
                    );
                    return v___x_5946_;
                } else {
                    v___f_5947_ = lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                    lean_closure_set(v___f_5947_, 0, v___x_5942_);
                    v___x_5948_ = lean_box(0);
                    v___x_5949_ = 0;
                    v___f_5950_ = lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_5950_, 0, v___f_5947_);
                    v___x_5951_ = lean_box((v___x_5949_) as usize);
                    v___x_5952_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5952_, 0, v___x_5951_);
                    lean_ctor_set(v___x_5952_, 1, v___f_5950_);
                    v___x_5953_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5953_, 0, v___x_5948_);
                    lean_ctor_set(v___x_5953_, 1, v___x_5952_);
                    v___x_5954_ = lean_array_get(v___x_5953_, v_declInfos_5866_, v___x_5943_);
                    lean_dec_ref_known(v___x_5953_, 2);
                    v_snd_5955_ = lean_ctor_get(v___x_5954_, 1);
                    lean_inc(v_snd_5955_);
                    v_fst_5956_ = lean_ctor_get(v___x_5954_, 0);
                    lean_inc(v_fst_5956_);
                    lean_dec(v___x_5954_);
                    v_fst_5957_ = lean_ctor_get(v_snd_5955_, 0);
                    lean_inc(v_fst_5957_);
                    v_snd_5958_ = lean_ctor_get(v_snd_5955_, 1);
                    lean_inc(v_snd_5958_);
                    lean_dec(v_snd_5955_);
                    lean_inc(v___y_5876_);
                    lean_inc_ref(v___y_5875_);
                    lean_inc(v___y_5874_);
                    lean_inc_ref(v___y_5873_);
                    lean_inc(v___y_5872_);
                    lean_inc_ref(v___y_5871_);
                    lean_inc_ref(v___y_5870_);
                    lean_inc_ref(v_acc_5869_);
                    v___x_5959_ = lean_apply_9(
                        v_snd_5958_,
                        v_acc_5869_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                        v___y_5874_,
                        v___y_5875_,
                        v___y_5876_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5959_) == 0 {
                        v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
                        lean_inc(v_a_5960_);
                        lean_dec_ref_known(v___x_5959_, 1);
                        v___x_5961_ = lean_box((v_kind_5868_) as usize);
                        v___f_5962_ = lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed as *mut core::ffi::c_void, 13, 4);
                        lean_closure_set(v___f_5962_, 0, v_acc_5869_);
                        lean_closure_set(v___f_5962_, 1, v_declInfos_5866_);
                        lean_closure_set(v___f_5962_, 2, v_k_5867_);
                        lean_closure_set(v___f_5962_, 3, v___x_5961_);
                        v___x_5963_ = (lean_unbox(v_fst_5957_) as u8);
                        lean_dec(v_fst_5957_);
                        v___x_5964_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_5956_, v___x_5963_, v_a_5960_, v___f_5962_, v_kind_5868_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                        return v___x_5964_;
                    } else {
                        lean_dec(v_fst_5957_);
                        lean_dec(v_fst_5956_);
                        lean_dec_ref(v_acc_5869_);
                        lean_dec_ref(v_k_5867_);
                        lean_dec_ref(v_declInfos_5866_);
                        return v___x_5959_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(
    mut v_acc_5977_: *mut LeanObject,
    mut v_declInfos_5978_: *mut LeanObject,
    mut v_k_5979_: *mut LeanObject,
    mut v_kind_5980_: u8,
    mut v_x_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
    mut v___y_5986_: *mut LeanObject,
    mut v___y_5987_: *mut LeanObject,
    mut v___y_5988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    v___x_5990_ = lean_array_push(v_acc_5977_, v_x_5981_);
    v___x_5991_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_5978_, v_k_5979_, v_kind_5980_, v___x_5990_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_);
    return v___x_5991_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(
    mut v_declInfos_5992_: *mut LeanObject,
    mut v_k_5993_: *mut LeanObject,
    mut v_kind_5994_: *mut LeanObject,
    mut v_acc_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_6004_: u8 = 0;
    let mut v_res_6005_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_6004_ = (lean_unbox(v_kind_5994_) as u8);
    v_res_6005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_5992_, v_k_5993_, v_kind_boxed_6004_, v_acc_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
    lean_dec(v___y_6002_);
    lean_dec_ref(v___y_6001_);
    lean_dec(v___y_6000_);
    lean_dec_ref(v___y_5999_);
    lean_dec(v___y_5998_);
    lean_dec_ref(v___y_5997_);
    lean_dec_ref(v___y_5996_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(
    mut v_declInfos_6008_: *mut LeanObject,
    mut v_k_6009_: *mut LeanObject,
    mut v_kind_6010_: u8,
    mut v___y_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
    mut v___y_6014_: *mut LeanObject,
    mut v___y_6015_: *mut LeanObject,
    mut v___y_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    v___x_6019_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0;
    v___x_6020_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_6008_, v_k_6009_, v_kind_6010_, v___x_6019_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_);
    return v___x_6020_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(
    mut v_declInfos_6021_: *mut LeanObject,
    mut v_k_6022_: *mut LeanObject,
    mut v_kind_6023_: *mut LeanObject,
    mut v___y_6024_: *mut LeanObject,
    mut v___y_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_6032_: u8 = 0;
    let mut v_res_6033_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_6032_ = (lean_unbox(v_kind_6023_) as u8);
    v_res_6033_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_6021_, v_k_6022_, v_kind_boxed_6032_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_);
    lean_dec(v___y_6030_);
    lean_dec_ref(v___y_6029_);
    lean_dec(v___y_6028_);
    lean_dec_ref(v___y_6027_);
    lean_dec(v___y_6026_);
    lean_dec_ref(v___y_6025_);
    lean_dec_ref(v___y_6024_);
    return v_res_6033_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(
    mut v_sz_6034_: usize,
    mut v_i_6035_: usize,
    mut v_bs_6036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6037_: u8 = 0;
    let mut v_v_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: usize = 0;
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut LeanObject = core::ptr::null_mut();
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
                    v_fst_6039_ = lean_ctor_get(v_v_6038_, 0);
                    v_snd_6040_ = lean_ctor_get(v_v_6038_, 1);
                    v_isSharedCheck_6056_ = (!lean_is_exclusive(v_v_6038_)) as u8;
                    if v_isSharedCheck_6056_ == 0 {
                        v___x_6042_ = v_v_6038_;
                        v_isShared_6043_ = v_isSharedCheck_6056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6040_);
                        lean_inc(v_fst_6039_);
                        lean_dec(v_v_6038_);
                        v___x_6042_ = lean_box(0);
                        v_isShared_6043_ = v_isSharedCheck_6056_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6044_ = lean_unsigned_to_nat(0);
                v_bs_x27_6045_ = lean_array_uset(v_bs_6036_, v_i_6035_, v___x_6044_);
                v___x_6046_ = 0;
                v___x_6047_ = lean_box((v___x_6046_) as usize);
                if v_isShared_6043_ == 0 {
                    lean_ctor_set(v___x_6042_, 0, v___x_6047_);
                    v___x_6049_ = v___x_6042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6047_);
                    lean_ctor_set(v_reuseFailAlloc_6055_, 1, v_snd_6040_);
                    v___x_6049_ = v_reuseFailAlloc_6055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6050_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6050_, 0, v_fst_6039_);
                lean_ctor_set(v___x_6050_, 1, v___x_6049_);
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
    mut v_sz_6057_: *mut LeanObject,
    mut v_i_6058_: *mut LeanObject,
    mut v_bs_6059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6060_: usize = 0;
    let mut v_i_boxed_6061_: usize = 0;
    let mut v_res_6062_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6060_ = lean_unbox_usize(v_sz_6057_);
    lean_dec(v_sz_6057_);
    v_i_boxed_6061_ = lean_unbox_usize(v_i_6058_);
    lean_dec(v_i_6058_);
    v_res_6062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_6060_, v_i_boxed_6061_, v_bs_6059_);
    return v_res_6062_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(
    mut v_declInfos_6063_: *mut LeanObject,
    mut v_k_6064_: *mut LeanObject,
    mut v_kind_6065_: u8,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6074_: usize = 0;
    let mut v___x_6075_: usize = 0;
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6074_ = lean_array_size(v_declInfos_6063_);
    v___x_6075_ = 0usize;
    v___x_6076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_6074_, v___x_6075_, v_declInfos_6063_);
    v___x_6077_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_6076_, v_k_6064_, v_kind_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
    return v___x_6077_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(
    mut v_declInfos_6078_: *mut LeanObject,
    mut v_k_6079_: *mut LeanObject,
    mut v_kind_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
    mut v___y_6082_: *mut LeanObject,
    mut v___y_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
    mut v___y_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_6089_: u8 = 0;
    let mut v_res_6090_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_6089_ = (lean_unbox(v_kind_6080_) as u8);
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
    lean_dec(v___y_6087_);
    lean_dec_ref(v___y_6086_);
    lean_dec(v___y_6085_);
    lean_dec_ref(v___y_6084_);
    lean_dec(v___y_6083_);
    lean_dec_ref(v___y_6082_);
    lean_dec_ref(v___y_6081_);
    return v_res_6090_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor(
    mut v_stx_6119_: *mut LeanObject,
    mut v_dec_6120_: *mut LeanObject,
    mut v_a_6121_: *mut LeanObject,
    mut v_a_6122_: *mut LeanObject,
    mut v_a_6123_: *mut LeanObject,
    mut v_a_6124_: *mut LeanObject,
    mut v_a_6125_: *mut LeanObject,
    mut v_a_6126_: *mut LeanObject,
    mut v_a_6127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: u8 = 0;
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: u8 = 0;
    let mut v___y_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: u8 = 0;
    let mut v___y_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: u8 = 0;
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6188_: u8 = 0;
    let mut v___y_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6237_: u8 = 0;
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6241_: u8 = 0;
    let mut v___y_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6248_: u8 = 0;
    let mut v___y_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6270_: u8 = 0;
    let mut v___y_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6289_: u8 = 0;
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6305_: u8 = 0;
    let mut v_fst_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_reuseFailAlloc_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut v_a_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6346_: u8 = 0;
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut v_a_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut v___y_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6371_: u8 = 0;
    let mut v___y_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6388_: u8 = 0;
    let mut v___y_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_returnsEarly_6394_: u8 = 0;
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6398_: usize = 0;
    let mut v___x_6399_: usize = 0;
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6402_: usize = 0;
    let mut v___x_6403_: usize = 0;
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: u8 = 0;
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6440_: u8 = 0;
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutVars_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u8 = 0;
    let mut v___x_6475_: u8 = 0;
    let mut v___x_6476_: usize = 0;
    let mut v___x_6477_: usize = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: usize = 0;
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v_a_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6497_: u8 = 0;
    let mut v_a_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6501_: u8 = 0;
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v_reuseFailAlloc_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_reuseFailAlloc_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut v_a_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6513_: u8 = 0;
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6517_: u8 = 0;
    let mut v_a_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6525_: u8 = 0;
    let mut v_a_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut v_a_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: u8 = 0;
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: u8 = 0;
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6129_ = l_Lean_Elab_Do_expandDoFor___closed__1;
                lean_inc(v_stx_6119_);
                v___x_6130_ = l_Lean_Syntax_isOfKind(v_stx_6119_, v___x_6129_);
                if v___x_6130_ == 0 {
                    lean_dec_ref(v_dec_6120_);
                    lean_dec(v_stx_6119_);
                    v___x_6131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                    return v___x_6131_;
                } else {
                    v___x_6132_ = lean_unsigned_to_nat(1);
                    v___x_6133_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6132_);
                    lean_inc(v___x_6133_);
                    v___x_6134_ = l_Lean_Syntax_matchesNull(v___x_6133_, v___x_6132_);
                    if v___x_6134_ == 0 {
                        lean_dec(v___x_6133_);
                        lean_dec_ref(v_dec_6120_);
                        lean_dec(v_stx_6119_);
                        v___x_6135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                        return v___x_6135_;
                    } else {
                        v___x_6136_ = lean_unsigned_to_nat(0);
                        v___x_6137_ = l_Lean_Syntax_getArg(v___x_6133_, v___x_6136_);
                        lean_dec(v___x_6133_);
                        v___x_6138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        lean_inc(v___x_6137_);
                        v___x_6139_ = l_Lean_Syntax_isOfKind(v___x_6137_, v___x_6138_);
                        if v___x_6139_ == 0 {
                            lean_dec(v___x_6137_);
                            lean_dec_ref(v_dec_6120_);
                            lean_dec(v_stx_6119_);
                            v___x_6407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                            return v___x_6407_;
                        } else {
                            v_tk_6408_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6136_);
                            v___x_6542_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6136_);
                            v___x_6543_ = l_Lean_Syntax_isNone(v___x_6542_);
                            if v___x_6543_ == 0 {
                                v___x_6544_ = lean_unsigned_to_nat(2);
                                lean_inc(v___x_6542_);
                                v___x_6545_ = l_Lean_Syntax_matchesNull(v___x_6542_, v___x_6544_);
                                if v___x_6545_ == 0 {
                                    lean_dec(v___x_6542_);
                                    lean_dec(v_tk_6408_);
                                    lean_dec(v___x_6137_);
                                    lean_dec_ref(v_dec_6120_);
                                    lean_dec(v_stx_6119_);
                                    v___x_6546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                                    return v___x_6546_;
                                } else {
                                    v_h_x3f_6547_ = l_Lean_Syntax_getArg(v___x_6542_, v___x_6136_);
                                    lean_dec(v___x_6542_);
                                    v___x_6548_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_6548_, 0, v_h_x3f_6547_);
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
                                lean_dec(v___x_6542_);
                                v___x_6549_ = lean_box(0);
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
                v___x_6168_ = lean_box((v___x_6139_) as usize);
                lean_inc(v___y_6142_);
                lean_inc(v___y_6154_);
                lean_inc(v___y_6152_);
                lean_inc_ref(v___y_6144_);
                lean_inc_ref(v___y_6150_);
                v___f_6169_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__9___boxed as *mut core::ffi::c_void,
                    24,
                    15,
                );
                lean_closure_set(v___f_6169_, 0, v___x_6167_);
                lean_closure_set(v___f_6169_, 1, v___x_6136_);
                lean_closure_set(v___f_6169_, 2, v___y_6156_);
                lean_closure_set(v___f_6169_, 3, v___y_6150_);
                lean_closure_set(v___f_6169_, 4, v___y_6144_);
                lean_closure_set(v___f_6169_, 5, v___y_6152_);
                lean_closure_set(v___f_6169_, 6, v___y_6146_);
                lean_closure_set(v___f_6169_, 7, v___y_6153_);
                lean_closure_set(v___f_6169_, 8, v___y_6147_);
                lean_closure_set(v___f_6169_, 9, v___y_6148_);
                lean_closure_set(v___f_6169_, 10, v___x_6168_);
                lean_closure_set(v___f_6169_, 11, v___y_6154_);
                lean_closure_set(v___f_6169_, 12, v___y_6142_);
                lean_closure_set(v___f_6169_, 13, v___y_6141_);
                lean_closure_set(v___f_6169_, 14, v___x_6132_);
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
                if lean_obj_tag(v___x_6171_) == 0 {
                    v_a_6172_ = lean_ctor_get(v___x_6171_, 0);
                    lean_inc(v_a_6172_);
                    lean_dec_ref_known(v___x_6171_, 1);
                    v_doBlockResultType_6173_ = lean_ctor_get(v___y_6159_, 3);
                    v___x_6174_ = lean_box((v___y_6145_) as usize);
                    lean_inc(v___y_6155_);
                    lean_inc_ref(v_doBlockResultType_6173_);
                    v___y_6175_ = lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__10___boxed as *mut core::ffi::c_void,
                        19,
                        11,
                    );
                    lean_closure_set(v___y_6175_, 0, v___x_6174_);
                    lean_closure_set(v___y_6175_, 1, v___y_6144_);
                    lean_closure_set(v___y_6175_, 2, v___y_6149_);
                    lean_closure_set(v___y_6175_, 3, v_doBlockResultType_6173_);
                    lean_closure_set(v___y_6175_, 4, v___y_6150_);
                    lean_closure_set(v___y_6175_, 5, v___y_6155_);
                    lean_closure_set(v___y_6175_, 6, v___y_6152_);
                    lean_closure_set(v___y_6175_, 7, v___y_6143_);
                    lean_closure_set(v___y_6175_, 8, v___y_6151_);
                    lean_closure_set(v___y_6175_, 9, v___x_6136_);
                    lean_closure_set(v___y_6175_, 10, v___x_6132_);
                    v___x_6176_ = lean_box((v___x_6139_) as usize);
                    v___f_6177_ = lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__11___boxed as *mut core::ffi::c_void,
                        13,
                        4,
                    );
                    lean_closure_set(v___f_6177_, 0, v___y_6154_);
                    lean_closure_set(v___f_6177_, 1, v___y_6175_);
                    lean_closure_set(v___f_6177_, 2, v___x_6132_);
                    lean_closure_set(v___f_6177_, 3, v___x_6176_);
                    lean_inc_ref(v___y_6165_);
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
                    if lean_obj_tag(v___x_6178_) == 0 {
                        v_a_6179_ = lean_ctor_get(v___x_6178_, 0);
                        lean_inc(v_a_6179_);
                        lean_dec_ref_known(v___x_6178_, 1);
                        v___x_6180_ = l_Lean_Expr_app___override(v___y_6164_, v_a_6172_);
                        lean_inc_ref(v_doBlockResultType_6173_);
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
                        lean_dec(v_a_6172_);
                        lean_dec_ref(v___y_6165_);
                        lean_dec_ref(v___y_6164_);
                        return v___x_6178_;
                    }
                } else {
                    lean_dec_ref(v___y_6165_);
                    lean_dec_ref(v___y_6164_);
                    lean_dec(v___y_6154_);
                    lean_dec(v___y_6152_);
                    lean_dec_ref(v___y_6151_);
                    lean_dec_ref(v___y_6150_);
                    lean_dec(v___y_6149_);
                    lean_dec_ref(v___y_6144_);
                    lean_dec_ref(v___y_6143_);
                    lean_dec(v___y_6142_);
                    return v___x_6171_;
                }
            }
            2 => {
                v___x_6216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17;
                v___x_6217_ = l_Lean_Core_mkFreshUserName(v___x_6216_, v___y_6214_, v___y_6215_);
                if lean_obj_tag(v___x_6217_) == 0 {
                    if lean_obj_tag(v___y_6204_) == 1 {
                        if lean_obj_tag(v_snd_6208_) == 1 {
                            lean_dec_ref(v___y_6203_);
                            v_a_6218_ = lean_ctor_get(v___x_6217_, 0);
                            lean_inc(v_a_6218_);
                            lean_dec_ref_known(v___x_6217_, 1);
                            v_val_6219_ = lean_ctor_get(v___y_6204_, 0);
                            lean_inc(v_val_6219_);
                            lean_dec_ref_known(v___y_6204_, 1);
                            v_val_6220_ = lean_ctor_get(v_snd_6208_, 0);
                            lean_inc(v_val_6220_);
                            lean_dec_ref_known(v_snd_6208_, 1);
                            v___f_6221_ = lean_alloc_closure(
                                l_Lean_Elab_Do_elabDoFor___lam__12___boxed
                                    as *mut core::ffi::c_void,
                                16,
                                7,
                            );
                            lean_closure_set(v___f_6221_, 0, v___y_6197_);
                            lean_closure_set(v___f_6221_, 1, v___y_6192_);
                            lean_closure_set(v___f_6221_, 2, v___x_6136_);
                            lean_closure_set(v___f_6221_, 3, v___y_6183_);
                            lean_closure_set(v___f_6221_, 4, v___y_6200_);
                            lean_closure_set(v___f_6221_, 5, v_val_6220_);
                            lean_closure_set(v___f_6221_, 6, v___y_6187_);
                            v___x_6222_ = l_Lean_TSyntax_getId(v___y_6206_);
                            lean_dec(v___y_6206_);
                            v___x_6223_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6223_, 0, v___x_6222_);
                            lean_ctor_set(v___x_6223_, 1, v___y_6205_);
                            v___x_6224_ = l_Lean_TSyntax_getId(v_val_6219_);
                            lean_dec(v_val_6219_);
                            v___x_6225_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6225_, 0, v___x_6224_);
                            lean_ctor_set(v___x_6225_, 1, v___f_6221_);
                            v___x_6226_ = lean_unsigned_to_nat(2);
                            v___x_6227_ = lean_mk_empty_array_with_capacity(v___x_6226_);
                            v___x_6228_ = lean_array_push(v___x_6227_, v___x_6223_);
                            v___x_6229_ = lean_array_push(v___x_6228_, v___x_6225_);
                            lean_inc_ref(v___y_6189_);
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
                            lean_dec(v___y_6206_);
                            lean_dec_ref(v___y_6205_);
                            lean_dec_ref(v___y_6200_);
                            lean_dec(v___y_6197_);
                            lean_dec(v___y_6192_);
                            lean_dec_ref(v___y_6187_);
                            lean_dec_ref(v___y_6183_);
                            v_a_6230_ = lean_ctor_get(v___x_6217_, 0);
                            lean_inc(v_a_6230_);
                            lean_dec_ref_known(v___x_6217_, 1);
                            v___x_6231_ = lean_apply_2(v___y_6203_, v___y_6204_, v_snd_6208_);
                            lean_inc_ref(v___y_6189_);
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
                        lean_dec(v___y_6206_);
                        lean_dec_ref(v___y_6205_);
                        lean_dec_ref(v___y_6200_);
                        lean_dec(v___y_6197_);
                        lean_dec(v___y_6192_);
                        lean_dec_ref(v___y_6187_);
                        lean_dec_ref(v___y_6183_);
                        v_a_6232_ = lean_ctor_get(v___x_6217_, 0);
                        lean_inc(v_a_6232_);
                        lean_dec_ref_known(v___x_6217_, 1);
                        v___x_6233_ = lean_apply_2(v___y_6203_, v___y_6204_, v_snd_6208_);
                        lean_inc_ref(v___y_6189_);
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
                    lean_dec(v_snd_6208_);
                    lean_dec_ref(v_fst_6207_);
                    lean_dec(v___y_6206_);
                    lean_dec_ref(v___y_6205_);
                    lean_dec(v___y_6204_);
                    lean_dec_ref(v___y_6203_);
                    lean_dec(v___y_6202_);
                    lean_dec_ref(v___y_6200_);
                    lean_dec(v___y_6199_);
                    lean_dec_ref(v___y_6198_);
                    lean_dec(v___y_6197_);
                    lean_dec(v___y_6196_);
                    lean_dec_ref(v___y_6195_);
                    lean_dec_ref(v___y_6194_);
                    lean_dec(v___y_6193_);
                    lean_dec(v___y_6192_);
                    lean_dec(v___y_6191_);
                    lean_dec(v___y_6190_);
                    lean_dec_ref(v___y_6189_);
                    lean_dec_ref(v___y_6187_);
                    lean_dec_ref(v___y_6186_);
                    lean_dec_ref(v___y_6185_);
                    lean_dec(v___y_6184_);
                    lean_dec_ref(v___y_6183_);
                    v_a_6234_ = lean_ctor_get(v___x_6217_, 0);
                    v_isSharedCheck_6241_ = (!lean_is_exclusive(v___x_6217_)) as u8;
                    if v_isSharedCheck_6241_ == 0 {
                        v___x_6236_ = v___x_6217_;
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6234_);
                        lean_dec(v___x_6217_);
                        v___x_6236_ = lean_box(0);
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
                    v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6239_;
            }
            5 => {
                v___x_6277_ = lean_box(0);
                lean_inc_ref(v___y_6255_);
                lean_inc(v___y_6259_);
                lean_inc_ref(v___y_6263_);
                lean_inc(v___y_6261_);
                lean_inc_ref(v___y_6273_);
                lean_inc(v___y_6266_);
                lean_inc_ref(v___y_6260_);
                v___x_6278_ = lean_apply_8(
                    v___y_6255_,
                    v___x_6277_,
                    v___y_6260_,
                    v___y_6266_,
                    v___y_6273_,
                    v___y_6261_,
                    v___y_6263_,
                    v___y_6259_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6278_) == 0 {
                    v_a_6279_ = lean_ctor_get(v___x_6278_, 0);
                    lean_inc(v_a_6279_);
                    lean_dec_ref_known(v___x_6278_, 1);
                    v_m_6280_ = lean_ctor_get(v___y_6274_, 0);
                    v_u_6281_ = lean_ctor_get(v___y_6274_, 1);
                    v_v_6282_ = lean_ctor_get(v___y_6274_, 2);
                    lean_inc(v_u_6281_);
                    v___x_6283_ = l_Lean_Meta_mkProdMkN(
                        v_a_6279_,
                        v_u_6281_,
                        v___y_6273_,
                        v___y_6261_,
                        v___y_6263_,
                        v___y_6259_,
                    );
                    if lean_obj_tag(v___x_6283_) == 0 {
                        v_a_6284_ = lean_ctor_get(v___x_6283_, 0);
                        lean_inc(v_a_6284_);
                        lean_dec_ref_known(v___x_6283_, 1);
                        if lean_obj_tag(v___y_6262_) == 0 {
                            v_fst_6285_ = lean_ctor_get(v_a_6284_, 0);
                            v_snd_6286_ = lean_ctor_get(v_a_6284_, 1);
                            v_isSharedCheck_6305_ = (!lean_is_exclusive(v_a_6284_)) as u8;
                            if v_isSharedCheck_6305_ == 0 {
                                v___x_6288_ = v_a_6284_;
                                v_isShared_6289_ = v_isSharedCheck_6305_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_snd_6286_);
                                lean_inc(v_fst_6285_);
                                lean_dec(v_a_6284_);
                                v___x_6288_ = lean_box(0);
                                v_isShared_6289_ = v_isSharedCheck_6305_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_fst_6306_ = lean_ctor_get(v_a_6284_, 0);
                            v_snd_6307_ = lean_ctor_get(v_a_6284_, 1);
                            v_isSharedCheck_6342_ = (!lean_is_exclusive(v_a_6284_)) as u8;
                            if v_isSharedCheck_6342_ == 0 {
                                v___x_6309_ = v_a_6284_;
                                v_isShared_6310_ = v_isSharedCheck_6342_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_snd_6307_);
                                lean_inc(v_fst_6306_);
                                lean_dec(v_a_6284_);
                                v___x_6309_ = lean_box(0);
                                v_isShared_6310_ = v_isSharedCheck_6342_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_6276_);
                        lean_dec(v___y_6275_);
                        lean_dec_ref(v___y_6272_);
                        lean_dec_ref(v___y_6269_);
                        lean_dec(v___y_6268_);
                        lean_dec(v___y_6267_);
                        lean_dec_ref(v___y_6265_);
                        lean_dec_ref(v___y_6264_);
                        lean_dec(v___y_6262_);
                        lean_dec_ref(v___y_6258_);
                        lean_dec(v___y_6257_);
                        lean_dec_ref(v___y_6256_);
                        lean_dec_ref(v___y_6255_);
                        lean_dec(v___y_6254_);
                        lean_dec_ref(v___y_6253_);
                        lean_dec_ref(v___y_6252_);
                        lean_dec(v___y_6251_);
                        lean_dec(v___y_6250_);
                        lean_dec(v___y_6249_);
                        lean_dec_ref(v___y_6247_);
                        lean_dec_ref(v___y_6246_);
                        lean_dec_ref(v___y_6245_);
                        lean_dec(v___y_6244_);
                        lean_dec_ref(v___y_6243_);
                        v_a_6343_ = lean_ctor_get(v___x_6283_, 0);
                        v_isSharedCheck_6350_ = (!lean_is_exclusive(v___x_6283_)) as u8;
                        if v_isSharedCheck_6350_ == 0 {
                            v___x_6345_ = v___x_6283_;
                            v_isShared_6346_ = v_isSharedCheck_6350_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_6343_);
                            lean_dec(v___x_6283_);
                            v___x_6345_ = lean_box(0);
                            v_isShared_6346_ = v_isSharedCheck_6350_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_6276_);
                    lean_dec(v___y_6275_);
                    lean_dec_ref(v___y_6272_);
                    lean_dec_ref(v___y_6269_);
                    lean_dec(v___y_6268_);
                    lean_dec(v___y_6267_);
                    lean_dec_ref(v___y_6265_);
                    lean_dec_ref(v___y_6264_);
                    lean_dec(v___y_6262_);
                    lean_dec_ref(v___y_6258_);
                    lean_dec(v___y_6257_);
                    lean_dec_ref(v___y_6256_);
                    lean_dec_ref(v___y_6255_);
                    lean_dec(v___y_6254_);
                    lean_dec_ref(v___y_6253_);
                    lean_dec_ref(v___y_6252_);
                    lean_dec(v___y_6251_);
                    lean_dec(v___y_6250_);
                    lean_dec(v___y_6249_);
                    lean_dec_ref(v___y_6247_);
                    lean_dec_ref(v___y_6246_);
                    lean_dec_ref(v___y_6245_);
                    lean_dec(v___y_6244_);
                    lean_dec_ref(v___y_6243_);
                    v_a_6351_ = lean_ctor_get(v___x_6278_, 0);
                    v_isSharedCheck_6358_ = (!lean_is_exclusive(v___x_6278_)) as u8;
                    if v_isSharedCheck_6358_ == 0 {
                        v___x_6353_ = v___x_6278_;
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_6351_);
                        lean_dec(v___x_6278_);
                        v___x_6353_ = lean_box(0);
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6290_ = l_Lean_Elab_Do_elabDoFor___closed__1;
                v___x_6291_ = lean_box(0);
                lean_inc(v_v_6282_);
                if v_isShared_6289_ == 0 {
                    lean_ctor_set_tag(v___x_6288_, 1);
                    lean_ctor_set(v___x_6288_, 1, v___x_6291_);
                    lean_ctor_set(v___x_6288_, 0, v_v_6282_);
                    v___x_6293_ = v___x_6288_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6304_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_v_6282_);
                    lean_ctor_set(v_reuseFailAlloc_6304_, 1, v___x_6291_);
                    v___x_6293_ = v_reuseFailAlloc_6304_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_inc(v_u_6281_);
                v___x_6294_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6294_, 0, v_u_6281_);
                lean_ctor_set(v___x_6294_, 1, v___x_6293_);
                v___x_6295_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6295_, 0, v___y_6267_);
                lean_ctor_set(v___x_6295_, 1, v___x_6294_);
                v___x_6296_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6296_, 0, v___y_6268_);
                lean_ctor_set(v___x_6296_, 1, v___x_6295_);
                lean_inc_ref(v___x_6296_);
                v___x_6297_ = l_Lean_mkConst(v___x_6290_, v___x_6296_);
                lean_inc_ref(v___y_6258_);
                lean_inc_ref(v___y_6272_);
                lean_inc_ref(v_m_6280_);
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
                if lean_obj_tag(v___x_6299_) == 0 {
                    v_a_6300_ = lean_ctor_get(v___x_6299_, 0);
                    lean_inc(v_a_6300_);
                    lean_dec_ref_known(v___x_6299_, 1);
                    v___x_6301_ = l_Lean_Elab_Do_elabDoFor___closed__3;
                    v___x_6302_ = l_Lean_mkConst(v___x_6301_, v___x_6296_);
                    lean_inc(v_snd_6286_);
                    lean_inc_ref(v_m_6280_);
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
                    lean_inc(v_u_6281_);
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
                    lean_dec_ref_known(v___x_6296_, 2);
                    lean_dec(v_snd_6286_);
                    lean_dec(v_fst_6285_);
                    lean_dec(v___y_6276_);
                    lean_dec(v___y_6275_);
                    lean_dec_ref(v___y_6272_);
                    lean_dec_ref(v___y_6269_);
                    lean_dec_ref(v___y_6265_);
                    lean_dec_ref(v___y_6264_);
                    lean_dec_ref(v___y_6258_);
                    lean_dec(v___y_6257_);
                    lean_dec_ref(v___y_6256_);
                    lean_dec_ref(v___y_6255_);
                    lean_dec(v___y_6254_);
                    lean_dec_ref(v___y_6253_);
                    lean_dec_ref(v___y_6252_);
                    lean_dec(v___y_6251_);
                    lean_dec(v___y_6250_);
                    lean_dec(v___y_6249_);
                    lean_dec_ref(v___y_6247_);
                    lean_dec_ref(v___y_6246_);
                    lean_dec_ref(v___y_6245_);
                    lean_dec(v___y_6244_);
                    lean_dec_ref(v___y_6243_);
                    return v___x_6299_;
                }
            }
            8 => {
                v___x_6311_ = l_Lean_Elab_Do_elabDoFor___closed__4;
                v___x_6312_ = lean_box(0);
                lean_inc(v___y_6268_);
                if v_isShared_6310_ == 0 {
                    lean_ctor_set_tag(v___x_6309_, 1);
                    lean_ctor_set(v___x_6309_, 1, v___x_6312_);
                    lean_ctor_set(v___x_6309_, 0, v___y_6268_);
                    v___x_6314_ = v___x_6309_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6341_, 0, v___y_6268_);
                    lean_ctor_set(v_reuseFailAlloc_6341_, 1, v___x_6312_);
                    v___x_6314_ = v_reuseFailAlloc_6341_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_inc(v___y_6267_);
                v___x_6315_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6315_, 0, v___y_6267_);
                lean_ctor_set(v___x_6315_, 1, v___x_6314_);
                v___x_6316_ = l_Lean_mkConst(v___x_6311_, v___x_6315_);
                lean_inc_ref(v___y_6272_);
                lean_inc_ref(v___y_6258_);
                v___x_6317_ = l_Lean_mkAppB(v___x_6316_, v___y_6258_, v___y_6272_);
                v___x_6318_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6318_, 0, v___x_6317_);
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
                if lean_obj_tag(v___x_6320_) == 0 {
                    v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
                    lean_inc_n(v_a_6321_, 2);
                    lean_dec_ref_known(v___x_6320_, 1);
                    v___x_6322_ = l_Lean_Elab_Do_elabDoFor___closed__8;
                    lean_inc(v_v_6282_);
                    v___x_6323_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6323_, 0, v_v_6282_);
                    lean_ctor_set(v___x_6323_, 1, v___x_6312_);
                    lean_inc(v_u_6281_);
                    v___x_6324_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6324_, 0, v_u_6281_);
                    lean_ctor_set(v___x_6324_, 1, v___x_6323_);
                    v___x_6325_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6325_, 0, v___y_6267_);
                    lean_ctor_set(v___x_6325_, 1, v___x_6324_);
                    v___x_6326_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6326_, 0, v___y_6268_);
                    lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                    lean_inc_ref(v___x_6326_);
                    v___x_6327_ = l_Lean_mkConst(v___x_6322_, v___x_6326_);
                    lean_inc_ref(v___y_6258_);
                    lean_inc_ref(v___y_6272_);
                    lean_inc_ref(v_m_6280_);
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
                    if lean_obj_tag(v___x_6329_) == 0 {
                        v_a_6330_ = lean_ctor_get(v___x_6329_, 0);
                        v_isSharedCheck_6340_ = (!lean_is_exclusive(v___x_6329_)) as u8;
                        if v_isSharedCheck_6340_ == 0 {
                            v___x_6332_ = v___x_6329_;
                            v_isShared_6333_ = v_isSharedCheck_6340_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_6330_);
                            lean_dec(v___x_6329_);
                            v___x_6332_ = lean_box(0);
                            v_isShared_6333_ = v_isSharedCheck_6340_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_6326_, 2);
                        lean_dec(v_a_6321_);
                        lean_dec(v_snd_6307_);
                        lean_dec_ref_known(v___y_6262_, 1);
                        lean_dec(v_fst_6306_);
                        lean_dec(v___y_6276_);
                        lean_dec(v___y_6275_);
                        lean_dec_ref(v___y_6272_);
                        lean_dec_ref(v___y_6269_);
                        lean_dec_ref(v___y_6265_);
                        lean_dec_ref(v___y_6264_);
                        lean_dec_ref(v___y_6258_);
                        lean_dec(v___y_6257_);
                        lean_dec_ref(v___y_6256_);
                        lean_dec_ref(v___y_6255_);
                        lean_dec(v___y_6254_);
                        lean_dec_ref(v___y_6253_);
                        lean_dec_ref(v___y_6252_);
                        lean_dec(v___y_6251_);
                        lean_dec(v___y_6250_);
                        lean_dec(v___y_6249_);
                        lean_dec_ref(v___y_6247_);
                        lean_dec_ref(v___y_6246_);
                        lean_dec_ref(v___y_6245_);
                        lean_dec(v___y_6244_);
                        lean_dec_ref(v___y_6243_);
                        return v___x_6329_;
                    }
                } else {
                    lean_dec(v_snd_6307_);
                    lean_dec_ref_known(v___y_6262_, 1);
                    lean_dec(v_fst_6306_);
                    lean_dec(v___y_6276_);
                    lean_dec(v___y_6275_);
                    lean_dec_ref(v___y_6272_);
                    lean_dec_ref(v___y_6269_);
                    lean_dec(v___y_6268_);
                    lean_dec(v___y_6267_);
                    lean_dec_ref(v___y_6265_);
                    lean_dec_ref(v___y_6264_);
                    lean_dec_ref(v___y_6258_);
                    lean_dec(v___y_6257_);
                    lean_dec_ref(v___y_6256_);
                    lean_dec_ref(v___y_6255_);
                    lean_dec(v___y_6254_);
                    lean_dec_ref(v___y_6253_);
                    lean_dec_ref(v___y_6252_);
                    lean_dec(v___y_6251_);
                    lean_dec(v___y_6250_);
                    lean_dec(v___y_6249_);
                    lean_dec_ref(v___y_6247_);
                    lean_dec_ref(v___y_6246_);
                    lean_dec_ref(v___y_6245_);
                    lean_dec(v___y_6244_);
                    lean_dec_ref(v___y_6243_);
                    return v___x_6320_;
                }
            }
            10 => {
                v___x_6334_ = l_Lean_Elab_Do_elabDoFor___closed__10;
                v___x_6335_ = l_Lean_mkConst(v___x_6334_, v___x_6326_);
                lean_inc(v_snd_6307_);
                lean_inc(v_a_6321_);
                lean_inc_ref(v_m_6280_);
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
                    lean_ctor_set_tag(v___x_6332_, 1);
                    lean_ctor_set(v___x_6332_, 0, v_a_6321_);
                    v___x_6338_ = v___x_6332_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6321_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc(v_u_6281_);
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
                    v_reuseFailAlloc_6349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6349_, 0, v_a_6343_);
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
                    v_reuseFailAlloc_6357_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
                    v___x_6356_ = v_reuseFailAlloc_6357_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6356_;
            }
            16 => {
                v_returnsEarly_6394_ = lean_ctor_get_uint8(
                    v___y_6378_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 2) as u32,
                );
                lean_dec_ref(v___y_6378_);
                v___x_6395_ = lean_box((v_returnsEarly_6394_) as usize);
                v___x_6396_ = lean_box((v___y_6371_) as usize);
                lean_inc_ref(v___y_6369_);
                lean_inc_ref(v___y_6375_);
                lean_inc_ref(v___y_6393_);
                v___f_6397_ = lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    6,
                );
                lean_closure_set(v___f_6397_, 0, v___y_6393_);
                lean_closure_set(v___f_6397_, 1, v___y_6375_);
                lean_closure_set(v___f_6397_, 2, v___x_6395_);
                lean_closure_set(v___f_6397_, 3, v___x_6136_);
                lean_closure_set(v___f_6397_, 4, v___y_6369_);
                lean_closure_set(v___f_6397_, 5, v___x_6396_);
                if v_returnsEarly_6394_ == 0 {
                    lean_dec(v___y_6385_);
                    v_sz_6398_ = lean_array_size(v___y_6393_);
                    v___x_6399_ = 0usize;
                    lean_inc_ref(v___y_6393_);
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
                    lean_inc_ref(v___y_6393_);
                    v___x_6404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_6402_, v___x_6403_, v___y_6393_);
                    v___x_6405_ = lean_array_to_list(v___x_6404_);
                    v___x_6406_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6406_, 0, v___y_6385_);
                    lean_ctor_set(v___x_6406_, 1, v___x_6405_);
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
                lean_inc(v_x_6418_);
                v___x_6420_ = l_Lean_Syntax_isOfKind(v_x_6418_, v___x_6419_);
                if v___x_6420_ == 0 {
                    lean_dec(v_x_6418_);
                    lean_dec(v_h_x3f_6410_);
                    lean_dec(v_tk_6408_);
                    lean_dec(v___x_6137_);
                    lean_dec_ref(v_dec_6120_);
                    lean_dec(v_stx_6119_);
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
                    lean_dec(v_tk_6408_);
                    if lean_obj_tag(v___x_6422_) == 0 {
                        v_a_6423_ = lean_ctor_get(v___x_6422_, 0);
                        lean_inc(v_a_6423_);
                        lean_dec_ref_known(v___x_6422_, 1);
                        v___x_6424_ = lean_mk_empty_array_with_capacity(v___x_6132_);
                        lean_inc(v_x_6418_);
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
                        lean_dec_ref(v___x_6425_);
                        if lean_obj_tag(v___x_6426_) == 0 {
                            lean_dec_ref_known(v___x_6426_, 1);
                            v___x_6427_ = l_Lean_Meta_mkFreshLevelMVar(
                                v___y_6414_,
                                v___y_6415_,
                                v___y_6416_,
                                v___y_6417_,
                            );
                            if lean_obj_tag(v___x_6427_) == 0 {
                                v_a_6428_ = lean_ctor_get(v___x_6427_, 0);
                                lean_inc(v_a_6428_);
                                lean_dec_ref_known(v___x_6427_, 1);
                                v___x_6429_ = l_Lean_Meta_mkFreshLevelMVar(
                                    v___y_6414_,
                                    v___y_6415_,
                                    v___y_6416_,
                                    v___y_6417_,
                                );
                                if lean_obj_tag(v___x_6429_) == 0 {
                                    v_a_6430_ = lean_ctor_get(v___x_6429_, 0);
                                    lean_inc(v_a_6430_);
                                    lean_dec_ref_known(v___x_6429_, 1);
                                    lean_inc(v_a_6428_);
                                    v___x_6431_ = l_Lean_Level_succ___override(v_a_6428_);
                                    v___x_6432_ = l_Lean_mkSort(v___x_6431_);
                                    v___x_6433_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_6433_, 0, v___x_6432_);
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
                                    if lean_obj_tag(v___x_6436_) == 0 {
                                        v_a_6437_ = lean_ctor_get(v___x_6436_, 0);
                                        v_isSharedCheck_6509_ =
                                            (!lean_is_exclusive(v___x_6436_)) as u8;
                                        if v_isSharedCheck_6509_ == 0 {
                                            v___x_6439_ = v___x_6436_;
                                            v_isShared_6440_ = v_isSharedCheck_6509_;
                                            state = 18;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6437_);
                                            lean_dec(v___x_6436_);
                                            v___x_6439_ = lean_box(0);
                                            v_isShared_6440_ = v_isSharedCheck_6509_;
                                            state = 18;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_6430_);
                                        lean_dec(v_a_6428_);
                                        lean_dec(v_a_6423_);
                                        lean_dec(v_x_6418_);
                                        lean_dec(v_h_x3f_6410_);
                                        lean_dec(v___x_6137_);
                                        lean_dec(v_stx_6119_);
                                        return v___x_6436_;
                                    }
                                } else {
                                    lean_dec(v_a_6428_);
                                    lean_dec(v_a_6423_);
                                    lean_dec(v_x_6418_);
                                    lean_dec(v_h_x3f_6410_);
                                    lean_dec(v___x_6137_);
                                    lean_dec(v_stx_6119_);
                                    v_a_6510_ = lean_ctor_get(v___x_6429_, 0);
                                    v_isSharedCheck_6517_ = (!lean_is_exclusive(v___x_6429_)) as u8;
                                    if v_isSharedCheck_6517_ == 0 {
                                        v___x_6512_ = v___x_6429_;
                                        v_isShared_6513_ = v_isSharedCheck_6517_;
                                        state = 28;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6510_);
                                        lean_dec(v___x_6429_);
                                        v___x_6512_ = lean_box(0);
                                        v_isShared_6513_ = v_isSharedCheck_6517_;
                                        state = 28;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6423_);
                                lean_dec(v_x_6418_);
                                lean_dec(v_h_x3f_6410_);
                                lean_dec(v___x_6137_);
                                lean_dec(v_stx_6119_);
                                v_a_6518_ = lean_ctor_get(v___x_6427_, 0);
                                v_isSharedCheck_6525_ = (!lean_is_exclusive(v___x_6427_)) as u8;
                                if v_isSharedCheck_6525_ == 0 {
                                    v___x_6520_ = v___x_6427_;
                                    v_isShared_6521_ = v_isSharedCheck_6525_;
                                    state = 30;
                                    continue;
                                } else {
                                    lean_inc(v_a_6518_);
                                    lean_dec(v___x_6427_);
                                    v___x_6520_ = lean_box(0);
                                    v_isShared_6521_ = v_isSharedCheck_6525_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6423_);
                            lean_dec(v_x_6418_);
                            lean_dec(v_h_x3f_6410_);
                            lean_dec(v___x_6137_);
                            lean_dec(v_stx_6119_);
                            v_a_6526_ = lean_ctor_get(v___x_6426_, 0);
                            v_isSharedCheck_6533_ = (!lean_is_exclusive(v___x_6426_)) as u8;
                            if v_isSharedCheck_6533_ == 0 {
                                v___x_6528_ = v___x_6426_;
                                v_isShared_6529_ = v_isSharedCheck_6533_;
                                state = 32;
                                continue;
                            } else {
                                lean_inc(v_a_6526_);
                                lean_dec(v___x_6426_);
                                v___x_6528_ = lean_box(0);
                                v_isShared_6529_ = v_isSharedCheck_6533_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_x_6418_);
                        lean_dec(v_h_x3f_6410_);
                        lean_dec(v___x_6137_);
                        lean_dec(v_stx_6119_);
                        v_a_6534_ = lean_ctor_get(v___x_6422_, 0);
                        v_isSharedCheck_6541_ = (!lean_is_exclusive(v___x_6422_)) as u8;
                        if v_isSharedCheck_6541_ == 0 {
                            v___x_6536_ = v___x_6422_;
                            v_isShared_6537_ = v_isSharedCheck_6541_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_6534_);
                            lean_dec(v___x_6422_);
                            v___x_6536_ = lean_box(0);
                            v_isShared_6537_ = v_isSharedCheck_6541_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            18 => {
                lean_inc(v_a_6430_);
                v___x_6441_ = l_Lean_Level_succ___override(v_a_6430_);
                v___x_6442_ = l_Lean_mkSort(v___x_6441_);
                if v_isShared_6440_ == 0 {
                    lean_ctor_set_tag(v___x_6439_, 1);
                    lean_ctor_set(v___x_6439_, 0, v___x_6442_);
                    v___x_6444_ = v___x_6439_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 0, v___x_6442_);
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
                if lean_obj_tag(v___x_6446_) == 0 {
                    v_a_6447_ = lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6507_ = (!lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6449_ = v___x_6446_;
                        v_isShared_6450_ = v_isSharedCheck_6507_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_6447_);
                        lean_dec(v___x_6446_);
                        v___x_6449_ = lean_box(0);
                        v_isShared_6450_ = v_isSharedCheck_6507_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6437_);
                    lean_dec(v_a_6430_);
                    lean_dec(v_a_6428_);
                    lean_dec(v_a_6423_);
                    lean_dec(v_x_6418_);
                    lean_dec(v_h_x3f_6410_);
                    lean_dec(v___x_6137_);
                    lean_dec(v_stx_6119_);
                    return v___x_6446_;
                }
            }
            20 => {
                v___x_6451_ = lean_unsigned_to_nat(3);
                v___x_6452_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6451_);
                lean_dec(v___x_6137_);
                lean_inc(v_a_6447_);
                if v_isShared_6450_ == 0 {
                    lean_ctor_set_tag(v___x_6449_, 1);
                    v___x_6454_ = v___x_6449_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6447_);
                    v___x_6454_ = v_reuseFailAlloc_6506_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_6455_ = lean_box(0);
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
                if lean_obj_tag(v___x_6456_) == 0 {
                    v_a_6457_ = lean_ctor_get(v___x_6456_, 0);
                    lean_inc(v_a_6457_);
                    lean_dec_ref_known(v___x_6456_, 1);
                    v_body_6458_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6451_);
                    lean_dec(v_stx_6119_);
                    lean_inc(v_body_6458_);
                    v___x_6459_ = l_Lean_Elab_Do_inferControlInfoSeq(
                        v_body_6458_,
                        v___y_6412_,
                        v___y_6413_,
                        v___y_6414_,
                        v___y_6415_,
                        v___y_6416_,
                        v___y_6417_,
                    );
                    if lean_obj_tag(v___x_6459_) == 0 {
                        v_a_6460_ = lean_ctor_get(v___x_6459_, 0);
                        lean_inc(v_a_6460_);
                        lean_dec_ref_known(v___x_6459_, 1);
                        v___x_6461_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_6411_);
                        if lean_obj_tag(v___x_6461_) == 0 {
                            v_a_6462_ = lean_ctor_get(v___x_6461_, 0);
                            lean_inc(v_a_6462_);
                            lean_dec_ref_known(v___x_6461_, 1);
                            v___x_6463_ = l_Lean_Elab_Do_elabDoFor___closed__16;
                            v___x_6464_ =
                                l_Lean_Core_mkFreshUserName(v___x_6463_, v___y_6416_, v___y_6417_);
                            if lean_obj_tag(v___x_6464_) == 0 {
                                v_a_6465_ = lean_ctor_get(v___x_6464_, 0);
                                lean_inc(v_a_6465_);
                                lean_dec_ref_known(v___x_6464_, 1);
                                v_monadInfo_6466_ = lean_ctor_get(v___y_6411_, 0);
                                v_mutVars_6467_ = lean_ctor_get(v___y_6411_, 1);
                                lean_inc(v_a_6437_);
                                v___f_6468_ = lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    10,
                                    1,
                                );
                                lean_closure_set(v___f_6468_, 0, v_a_6437_);
                                lean_inc_ref(v___f_6468_);
                                lean_inc(v_x_6418_);
                                v___f_6469_ = lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__2___boxed
                                        as *mut core::ffi::c_void,
                                    5,
                                    3,
                                );
                                lean_closure_set(v___f_6469_, 0, v_x_6418_);
                                lean_closure_set(v___f_6469_, 1, v___f_6468_);
                                lean_closure_set(v___f_6469_, 2, v___x_6132_);
                                v___x_6470_ = lean_box((v___x_6139_) as usize);
                                lean_inc(v_a_6462_);
                                v___f_6471_ = lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                lean_closure_set(v___f_6471_, 0, v_a_6462_);
                                lean_closure_set(v___f_6471_, 1, v___x_6132_);
                                lean_closure_set(v___f_6471_, 2, v___x_6470_);
                                v___x_6472_ = lean_array_get_size(v_mutVars_6467_);
                                v___x_6473_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                                v___x_6474_ = lean_nat_dec_lt(v___x_6136_, v___x_6472_);
                                if v___x_6474_ == 0 {
                                    lean_inc(v_x_6418_);
                                    lean_inc(v_a_6447_);
                                    lean_inc(v_a_6430_);
                                    lean_inc(v_a_6465_);
                                    lean_inc(v_a_6428_);
                                    lean_inc(v_a_6457_);
                                    lean_inc(v_h_x3f_6410_);
                                    lean_inc(v_a_6437_);
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
                                            lean_inc(v_x_6418_);
                                            lean_inc(v_a_6447_);
                                            lean_inc(v_a_6430_);
                                            lean_inc(v_a_6465_);
                                            lean_inc(v_a_6428_);
                                            lean_inc(v_a_6457_);
                                            lean_inc(v_h_x3f_6410_);
                                            lean_inc(v_a_6437_);
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
                                            lean_inc(v_x_6418_);
                                            lean_inc(v_a_6447_);
                                            lean_inc(v_a_6430_);
                                            lean_inc(v_a_6465_);
                                            lean_inc(v_a_6428_);
                                            lean_inc(v_a_6457_);
                                            lean_inc(v_h_x3f_6410_);
                                            lean_inc(v_a_6437_);
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
                                        lean_inc(v_x_6418_);
                                        lean_inc(v_a_6447_);
                                        lean_inc(v_a_6430_);
                                        lean_inc(v_a_6465_);
                                        lean_inc(v_a_6428_);
                                        lean_inc(v_a_6457_);
                                        lean_inc(v_h_x3f_6410_);
                                        lean_inc(v_a_6437_);
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
                                lean_dec(v_a_6462_);
                                lean_dec(v_a_6460_);
                                lean_dec(v_body_6458_);
                                lean_dec(v_a_6457_);
                                lean_dec(v_a_6447_);
                                lean_dec(v_a_6437_);
                                lean_dec(v_a_6430_);
                                lean_dec(v_a_6428_);
                                lean_dec(v_a_6423_);
                                lean_dec(v_x_6418_);
                                lean_dec(v_h_x3f_6410_);
                                v_a_6482_ = lean_ctor_get(v___x_6464_, 0);
                                v_isSharedCheck_6489_ = (!lean_is_exclusive(v___x_6464_)) as u8;
                                if v_isSharedCheck_6489_ == 0 {
                                    v___x_6484_ = v___x_6464_;
                                    v_isShared_6485_ = v_isSharedCheck_6489_;
                                    state = 22;
                                    continue;
                                } else {
                                    lean_inc(v_a_6482_);
                                    lean_dec(v___x_6464_);
                                    v___x_6484_ = lean_box(0);
                                    v_isShared_6485_ = v_isSharedCheck_6489_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6460_);
                            lean_dec(v_body_6458_);
                            lean_dec(v_a_6457_);
                            lean_dec(v_a_6447_);
                            lean_dec(v_a_6437_);
                            lean_dec(v_a_6430_);
                            lean_dec(v_a_6428_);
                            lean_dec(v_a_6423_);
                            lean_dec(v_x_6418_);
                            lean_dec(v_h_x3f_6410_);
                            v_a_6490_ = lean_ctor_get(v___x_6461_, 0);
                            v_isSharedCheck_6497_ = (!lean_is_exclusive(v___x_6461_)) as u8;
                            if v_isSharedCheck_6497_ == 0 {
                                v___x_6492_ = v___x_6461_;
                                v_isShared_6493_ = v_isSharedCheck_6497_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_6490_);
                                lean_dec(v___x_6461_);
                                v___x_6492_ = lean_box(0);
                                v_isShared_6493_ = v_isSharedCheck_6497_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_body_6458_);
                        lean_dec(v_a_6457_);
                        lean_dec(v_a_6447_);
                        lean_dec(v_a_6437_);
                        lean_dec(v_a_6430_);
                        lean_dec(v_a_6428_);
                        lean_dec(v_a_6423_);
                        lean_dec(v_x_6418_);
                        lean_dec(v_h_x3f_6410_);
                        v_a_6498_ = lean_ctor_get(v___x_6459_, 0);
                        v_isSharedCheck_6505_ = (!lean_is_exclusive(v___x_6459_)) as u8;
                        if v_isSharedCheck_6505_ == 0 {
                            v___x_6500_ = v___x_6459_;
                            v_isShared_6501_ = v_isSharedCheck_6505_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_6498_);
                            lean_dec(v___x_6459_);
                            v___x_6500_ = lean_box(0);
                            v_isShared_6501_ = v_isSharedCheck_6505_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_6447_);
                    lean_dec(v_a_6437_);
                    lean_dec(v_a_6430_);
                    lean_dec(v_a_6428_);
                    lean_dec(v_a_6423_);
                    lean_dec(v_x_6418_);
                    lean_dec(v_h_x3f_6410_);
                    lean_dec(v_stx_6119_);
                    return v___x_6456_;
                }
            }
            22 => {
                if v_isShared_6485_ == 0 {
                    v___x_6487_ = v___x_6484_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_a_6482_);
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
                    v_reuseFailAlloc_6496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_a_6490_);
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
                    v_reuseFailAlloc_6504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
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
                    v_reuseFailAlloc_6516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6516_, 0, v_a_6510_);
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
                    v_reuseFailAlloc_6524_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_a_6518_);
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
                    v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
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
                    v_reuseFailAlloc_6540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
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
    mut v_stx_6550_: *mut LeanObject,
    mut v_dec_6551_: *mut LeanObject,
    mut v_a_6552_: *mut LeanObject,
    mut v_a_6553_: *mut LeanObject,
    mut v_a_6554_: *mut LeanObject,
    mut v_a_6555_: *mut LeanObject,
    mut v_a_6556_: *mut LeanObject,
    mut v_a_6557_: *mut LeanObject,
    mut v_a_6558_: *mut LeanObject,
    mut v_a_6559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6560_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6558_);
    lean_dec_ref(v_a_6557_);
    lean_dec(v_a_6556_);
    lean_dec_ref(v_a_6555_);
    lean_dec(v_a_6554_);
    lean_dec_ref(v_a_6553_);
    lean_dec_ref(v_a_6552_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(
    mut v_00_u03b1_6561_: *mut LeanObject,
    mut v_msg_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6571_: *mut LeanObject,
    mut v_msg_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6580_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6578_);
    lean_dec_ref(v___y_6577_);
    lean_dec(v___y_6576_);
    lean_dec_ref(v___y_6575_);
    lean_dec(v___y_6574_);
    lean_dec_ref(v___y_6573_);
    return v_res_6580_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(
    mut v_00_u03b1_6581_: *mut LeanObject,
    mut v_name_6582_: *mut LeanObject,
    mut v_type_6583_: *mut LeanObject,
    mut v_k_6584_: *mut LeanObject,
    mut v___y_6585_: *mut LeanObject,
    mut v___y_6586_: *mut LeanObject,
    mut v___y_6587_: *mut LeanObject,
    mut v___y_6588_: *mut LeanObject,
    mut v___y_6589_: *mut LeanObject,
    mut v___y_6590_: *mut LeanObject,
    mut v___y_6591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6594_: *mut LeanObject,
    mut v_name_6595_: *mut LeanObject,
    mut v_type_6596_: *mut LeanObject,
    mut v_k_6597_: *mut LeanObject,
    mut v___y_6598_: *mut LeanObject,
    mut v___y_6599_: *mut LeanObject,
    mut v___y_6600_: *mut LeanObject,
    mut v___y_6601_: *mut LeanObject,
    mut v___y_6602_: *mut LeanObject,
    mut v___y_6603_: *mut LeanObject,
    mut v___y_6604_: *mut LeanObject,
    mut v___y_6605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6606_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6604_);
    lean_dec_ref(v___y_6603_);
    lean_dec(v___y_6602_);
    lean_dec_ref(v___y_6601_);
    lean_dec(v___y_6600_);
    lean_dec_ref(v___y_6599_);
    lean_dec_ref(v___y_6598_);
    return v_res_6606_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(
    mut v_msgData_6607_: *mut LeanObject,
    mut v_macroStack_6608_: *mut LeanObject,
    mut v___y_6609_: *mut LeanObject,
    mut v___y_6610_: *mut LeanObject,
    mut v___y_6611_: *mut LeanObject,
    mut v___y_6612_: *mut LeanObject,
    mut v___y_6613_: *mut LeanObject,
    mut v___y_6614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    v___x_6616_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_6607_, v_macroStack_6608_, v___y_6613_);
    return v___x_6616_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(
    mut v_msgData_6617_: *mut LeanObject,
    mut v_macroStack_6618_: *mut LeanObject,
    mut v___y_6619_: *mut LeanObject,
    mut v___y_6620_: *mut LeanObject,
    mut v___y_6621_: *mut LeanObject,
    mut v___y_6622_: *mut LeanObject,
    mut v___y_6623_: *mut LeanObject,
    mut v___y_6624_: *mut LeanObject,
    mut v___y_6625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6626_: *mut LeanObject = core::ptr::null_mut();
    v_res_6626_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_6617_, v_macroStack_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
    lean_dec(v___y_6624_);
    lean_dec_ref(v___y_6623_);
    lean_dec(v___y_6622_);
    lean_dec_ref(v___y_6621_);
    lean_dec(v___y_6620_);
    lean_dec_ref(v___y_6619_);
    return v_res_6626_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1()
-> *mut LeanObject {
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    v___x_6634_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_6635_ = l_Lean_Elab_Do_expandDoFor___closed__1;
    v___x_6636_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1;
    v___x_6637_ = lean_alloc_closure(
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
    mut v_a_6639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6640_: *mut LeanObject = core::ptr::null_mut();
    v_res_6640_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
    return v_res_6640_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_For(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ProdN(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_For(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_For(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ProdN(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_For(builtin);
}
