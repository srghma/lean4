// Lean compiler output
// Module: Lean.Elab.ComputedFields
// Imports: Lean.Meta.Constructions.CasesOn Lean.Compiler.ImplementedByAttr Lean.Elab.PreDefinition.WF.Eqns Lean.Compiler.ExternAttr
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_Pi_instInhabited___redArg___lam__0, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::Attributes::{l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute};
use crate::r#gen::Lean::AuxRecursor::l_Lean_mkCasesOnName;
use crate::r#gen::Lean::Compiler::ExternAttr::{
    initialize_Lean_Compiler_ExternAttr, l_Lean_isExtern,
    runtime_initialize_Lean_Compiler_ExternAttr,
};
use crate::r#gen::Lean::Compiler::ImplementedByAttr::{
    initialize_Lean_Compiler_ImplementedByAttr, l_Lean_Compiler_setImplementedBy,
    runtime_initialize_Lean_Compiler_ImplementedByAttr,
};
use crate::r#gen::Lean::Compiler::InlineAttrs::l_Lean_Compiler_getInlineAttribute_x3f;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_compileDecls,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_updatePrefix,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::PreDefinition::WF::Eqns::{
    initialize_Lean_Elab_PreDefinition_WF_Eqns, l_Lean_Elab_WF_eqnInfoExt,
    l_Lean_Elab_WF_instInhabitedEqnInfo_default,
    runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_MapDeclarationExtension_find_x3f___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_setExporting,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_constName_x21, l_Lean_Expr_containsFVar, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_isImplementationDetail;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_indentExpr,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkAppM, l_Lean_Meta_mkAppOptM};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_Context_config, l_Lean_Meta_addZetaDeltaFVarId___redArg,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_instantiateForall,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_setInlineAttribute,
};
use crate::r#gen::Lean::Meta::Constructions::CasesOn::{
    initialize_Lean_Meta_Constructions_CasesOn, l_Lean_mkCasesOn,
    runtime_initialize_Lean_Meta_Constructions_CasesOn,
};
use crate::r#gen::Lean::Meta::WHNF::{
    l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go, l_Lean_Meta_unfoldDefinition,
    l_Lean_Meta_unfoldDefinition_x3f,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_MetavarContext_getExprAssignmentCore_x3f;
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::Util::FindExpr::l_Lean_Expr_occurs;
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParams;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_5, lean_apply_6, lean_apply_7, lean_apply_8, lean_box, lean_box_usize,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<84> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 84, m_capacity: 84, m_length: 83, m_data: [84, 104, 101, 32, 96, 91, 99, 111, 109, 112, 117, 116, 101, 100, 95, 102, 105, 101, 108, 100, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 119, 105, 116, 104, 45, 98, 108, 111, 99, 107, 32, 111, 102, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 108, 97, 98, 111, 114, 97, 116, 105, 110, 103, 67, 111, 109, 112, 117, 116, 101, 100, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject,6109398933489059627 as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [99, 111, 109, 112, 117, 116, 101, 100, 95, 102, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject,17593983999535818205 as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 99, 111, 109, 112, 117, 116, 101, 100, 32, 102, 105, 101, 108, 100, 32, 111, 102, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [67, 111, 109, 112, 117, 116, 101, 100, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [99, 111, 109, 112, 117, 116, 101, 100, 70, 105, 101, 108, 100, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject,1773629922848794941 as *mut LeanObject] };
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject,7810152543549283581 as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value: LeanStringObject<538> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 538, m_capacity: 538, m_length: 529, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 99, 111, 109, 112, 117, 116, 101, 100, 32, 102, 105, 101, 108, 100, 32, 111, 102, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 46, 10, 10, 67, 111, 109, 112, 117, 116, 101, 100, 32, 102, 105, 101, 108, 100, 115, 32, 97, 114, 101, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 119, 105, 116, 104, 45, 98, 108, 111, 99, 107, 32, 111, 102, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 32, 84, 104, 101, 121, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 10, 116, 111, 32, 97, 108, 108, 111, 119, 32, 99, 101, 114, 116, 97, 105, 110, 32, 118, 97, 108, 117, 101, 115, 32, 116, 111, 32, 98, 101, 32, 99, 111, 109, 112, 117, 116, 101, 100, 32, 111, 110, 108, 121, 32, 111, 110, 99, 101, 32, 97, 116, 32, 116, 104, 101, 32, 116, 105, 109, 101, 32, 111, 102, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 32, 97, 110, 100, 32, 116, 104, 101, 110, 32, 108, 97, 116, 101, 114, 32, 98, 101, 10, 97, 99, 99, 101, 115, 115, 101, 100, 32, 105, 109, 109, 101, 100, 105, 97, 116, 101, 108, 121, 46, 10, 10, 69, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 78, 97, 116, 76, 105, 115, 116, 32, 119, 104, 101, 114, 101, 10, 32, 32, 124, 32, 110, 105, 108, 10, 32, 32, 124, 32, 99, 111, 110, 115, 32, 58, 32, 78, 97, 116, 32, 226, 134, 146, 32, 78, 97, 116, 76, 105, 115, 116, 32, 226, 134, 146, 32, 78, 97, 116, 76, 105, 115, 116, 10, 119, 105, 116, 104, 10, 32, 32, 64, 91, 99, 111, 109, 112, 117, 116, 101, 100, 95, 102, 105, 101, 108, 100, 93, 32, 115, 117, 109, 32, 58, 32, 78, 97, 116, 76, 105, 115, 116, 32, 226, 134, 146, 32, 78, 97, 116, 10, 32, 32, 124, 32, 46, 110, 105, 108, 32, 61, 62, 32, 48, 10, 32, 32, 124, 32, 46, 99, 111, 110, 115, 32, 120, 32, 108, 32, 61, 62, 32, 120, 32, 43, 32, 108, 46, 115, 117, 109, 10, 32, 32, 64, 91, 99, 111, 109, 112, 117, 116, 101, 100, 95, 102, 105, 101, 108, 100, 93, 32, 108, 101, 110, 103, 116, 104, 32, 58, 32, 78, 97, 116, 76, 105, 115, 116, 32, 226, 134, 146, 32, 78, 97, 116, 10, 32, 32, 124, 32, 46, 110, 105, 108, 32, 61, 62, 32, 48, 10, 32, 32, 124, 32, 46, 99, 111, 110, 115, 32, 95, 32, 108, 32, 61, 62, 32, 108, 46, 108, 101, 110, 103, 116, 104, 32, 43, 32, 49, 10, 96, 96, 96, 10, 0]};
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 41 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 66 as usize) << 1) | 1) as *mut LeanObject,((( 102 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 102 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 63 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 63 as usize) << 1) | 1) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0_value: LeanStringObject<11> =
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
        m_data: [117, 110, 115, 97, 102, 101, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__0_value)
                as *mut LeanObject,
            9183409343678294206 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6_value) as *mut LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [108, 111, 111, 115, 101, 32, 98, 118, 97, 114, 32, 105, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 119, 104, 110, 102, 69, 97, 115, 121, 67, 97, 115, 101, 115, 0]};
static mut l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 87, 72, 78, 70, 0]};
static mut l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        99, 111, 109, 112, 117, 116, 101, 100, 32, 102, 105, 101, 108, 100, 32, 0,
    ],
};
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2_value: LeanStringObject<
    34,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101, 100, 117, 99, 101, 32, 102, 111,
        114, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [39, 115, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 100, 101, 112, 101, 110, 100, 32, 111, 110, 32, 105, 110, 100, 105, 99, 101, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [39, 115, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 100, 101, 112, 101, 110, 100, 32, 111, 110, 32, 118, 97, 108, 117, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 105, 109, 112, 108, 0]};
static mut l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__0_value) as *mut LeanObject,5783369521560178306 as *mut LeanObject] };
static mut l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [109, 0],
};
static mut l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__0_value)
            as *mut LeanObject,
        9694982152043229093 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [97, 0],
};
static mut l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__0_value)
            as *mut LeanObject,
        7839396180116328695 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 68, 101, 102, 110, 63, 0]};
static mut l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value: LeanStringObject<10> =
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
        m_data: [95, 111, 118, 101, 114, 114, 105, 100, 101, 0],
    };
static mut l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__0_value)
                as *mut LeanObject,
            5964785654722272588 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut LeanObject)] };
pub static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__0_value)
                as *mut LeanObject,
            13655884332201764339 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0_value: LeanStringObject<
    50,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        99, 111, 109, 112, 117, 116, 101, 100, 32, 102, 105, 101, 108, 100, 115, 32, 114, 101, 113,
        117, 105, 114, 101, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 116, 119, 111, 32, 99,
        111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 0,
    ],
};
static mut l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [39, 32, 109, 117, 115, 116, 32, 98, 101, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 64, 91, 99, 111, 109, 112, 117, 116, 101, 100, 95, 102, 105, 101, 108, 100, 93, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ComputedFields_setComputedFields___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_ComputedFields_setComputedFields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ComputedFields_setComputedFields___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    v___x_4664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4664_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    v___x_4665_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_4666_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4666_, 0, v___x_4665_);
    return v___x_4666_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_4668_ = lean_unsigned_to_nat(0);
    v___x_4669_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4669_, 0, v___x_4668_);
    lean_ctor_set(v___x_4669_, 1, v___x_4668_);
    lean_ctor_set(v___x_4669_, 2, v___x_4668_);
    lean_ctor_set(v___x_4669_, 3, v___x_4668_);
    lean_ctor_set(v___x_4669_, 4, v___x_4667_);
    lean_ctor_set(v___x_4669_, 5, v___x_4667_);
    lean_ctor_set(v___x_4669_, 6, v___x_4667_);
    lean_ctor_set(v___x_4669_, 7, v___x_4667_);
    lean_ctor_set(v___x_4669_, 8, v___x_4667_);
    lean_ctor_set(v___x_4669_, 9, v___x_4667_);
    return v___x_4669_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    v___x_4670_ = lean_unsigned_to_nat(32);
    v___x_4671_ = lean_mk_empty_array_with_capacity(v___x_4670_);
    v___x_4672_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4672_, 0, v___x_4671_);
    return v___x_4672_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4673_: usize = 0;
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    v___x_4673_ = 5usize;
    v___x_4674_ = lean_unsigned_to_nat(0);
    v___x_4675_ = lean_unsigned_to_nat(32);
    v___x_4676_ = lean_mk_empty_array_with_capacity(v___x_4675_);
    v___x_4677_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_4678_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4678_, 0, v___x_4677_);
    lean_ctor_set(v___x_4678_, 1, v___x_4676_);
    lean_ctor_set(v___x_4678_, 2, v___x_4674_);
    lean_ctor_set(v___x_4678_, 3, v___x_4674_);
    lean_ctor_set_usize(v___x_4678_, 4, v___x_4673_);
    return v___x_4678_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    v___x_4679_ = lean_box(1);
    v___x_4680_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_4681_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_4682_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4682_, 0, v___x_4681_);
    lean_ctor_set(v___x_4682_, 1, v___x_4680_);
    lean_ctor_set(v___x_4682_, 2, v___x_4679_);
    return v___x_4682_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    v___x_4687_ = lean_st_ref_get(v___y_4685_);
    v_env_4688_ = lean_ctor_get(v___x_4687_, 0);
    lean_inc_ref(v_env_4688_);
    lean_dec(v___x_4687_);
    v_options_4689_ = lean_ctor_get(v___y_4684_, 2);
    v___x_4690_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_4691_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_4689_);
    v___x_4692_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4692_, 0, v_env_4688_);
    lean_ctor_set(v___x_4692_, 1, v___x_4690_);
    lean_ctor_set(v___x_4692_, 2, v___x_4691_);
    lean_ctor_set(v___x_4692_, 3, v_options_4689_);
    v___x_4693_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4693_, 0, v___x_4692_);
    lean_ctor_set(v___x_4693_, 1, v_msgData_4683_);
    v___x_4694_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4694_, 0, v___x_4693_);
    return v___x_4694_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
    mut v___y_4698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4699_: *mut LeanObject = core::ptr::null_mut();
    v_res_4699_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_4695_, v___y_4696_, v___y_4697_);
    lean_dec(v___y_4697_);
    lean_dec_ref(v___y_4696_);
    return v_res_4699_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4704_ = lean_ctor_get(v___y_4701_, 5);
                v___x_4705_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_4700_, v___y_4701_, v___y_4702_);
                v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
                v_isSharedCheck_4714_ = (!lean_is_exclusive(v___x_4705_)) as u8;
                if v_isSharedCheck_4714_ == 0 {
                    v___x_4708_ = v___x_4705_;
                    v_isShared_4709_ = v_isSharedCheck_4714_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4706_);
                    lean_dec(v___x_4705_);
                    v___x_4708_ = lean_box(0);
                    v_isShared_4709_ = v_isSharedCheck_4714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4704_);
                v___x_4710_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4710_, 0, v_ref_4704_);
                lean_ctor_set(v___x_4710_, 1, v_a_4706_);
                if v_isShared_4709_ == 0 {
                    lean_ctor_set_tag(v___x_4708_, 1);
                    lean_ctor_set(v___x_4708_, 0, v___x_4710_);
                    v___x_4712_ = v___x_4708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_4715_: *mut LeanObject,
    mut v___y_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
    mut v___y_4718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4719_: *mut LeanObject = core::ptr::null_mut();
    v_res_4719_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_4715_, v___y_4716_, v___y_4717_);
    lean_dec(v___y_4717_);
    lean_dec_ref(v___y_4716_);
    return v_res_4719_;
}
pub unsafe fn _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    v___x_4721_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4722_ = l_Lean_stringToMessageData(v___x_4721_);
    return v___x_4722_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(
    mut v_x_4726_: *mut LeanObject,
    mut v___y_4727_: *mut LeanObject,
    mut v___y_4728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v_v_4741_: u8 = 0;
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4733_ = lean_ctor_get(v___y_4727_, 2);
                v_map_4734_ = lean_ctor_get(v_options_4733_, 0);
                v___x_4735_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
                v___x_4736_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4734_, v___x_4735_);
                if lean_obj_tag(v___x_4736_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4737_ = lean_ctor_get(v___x_4736_, 0);
                    v_isSharedCheck_4746_ = (!lean_is_exclusive(v___x_4736_)) as u8;
                    if v_isSharedCheck_4746_ == 0 {
                        v___x_4739_ = v___x_4736_;
                        v_isShared_4740_ = v_isSharedCheck_4746_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4737_);
                        lean_dec(v___x_4736_);
                        v___x_4739_ = lean_box(0);
                        v_isShared_4740_ = v_isSharedCheck_4746_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4731_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
                v___x_4732_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_4731_, v___y_4727_, v___y_4728_);
                return v___x_4732_;
            }
            2 => {
                if lean_obj_tag(v_val_4737_) == 1 {
                    v_v_4741_ = lean_ctor_get_uint8(v_val_4737_, 0 as u32);
                    lean_dec_ref_known(v_val_4737_, 0);
                    if v_v_4741_ == 0 {
                        lean_del_object(v___x_4739_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4742_ = lean_box(0);
                        if v_isShared_4740_ == 0 {
                            lean_ctor_set_tag(v___x_4739_, 0);
                            lean_ctor_set(v___x_4739_, 0, v___x_4742_);
                            v___x_4744_ = v___x_4739_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4742_);
                            v___x_4744_ = v_reuseFailAlloc_4745_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4739_);
                    lean_dec(v_val_4737_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_4744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(
    mut v_x_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4751_: *mut LeanObject = core::ptr::null_mut();
    v_res_4751_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_4747_, v___y_4748_, v___y_4749_);
    lean_dec(v___y_4749_);
    lean_dec_ref(v___y_4748_);
    lean_dec(v_x_4747_);
    return v_res_4751_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: u8 = 0;
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    v___f_4767_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4768_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4769_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4770_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4771_ = 0;
    v___x_4772_ = lean_box(2);
    v___x_4773_ = l_Lean_registerTagAttribute(
        v___x_4768_,
        v___x_4769_,
        v___f_4767_,
        v___x_4770_,
        v___x_4771_,
        v___x_4772_,
    );
    return v___x_4773_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(
    mut v_a_4774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4775_: *mut LeanObject = core::ptr::null_mut();
    v_res_4775_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
    return v_res_4775_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_4776_: *mut LeanObject,
    mut v_msg_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    v___x_4781_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_4777_, v___y_4778_, v___y_4779_);
    return v___x_4781_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_4782_: *mut LeanObject,
    mut v_msg_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4787_: *mut LeanObject = core::ptr::null_mut();
    v_res_4787_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_4782_, v_msg_4783_, v___y_4784_, v___y_4785_);
    lean_dec(v___y_4785_);
    lean_dec_ref(v___y_4784_);
    return v_res_4787_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    v___x_4790_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4791_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0;
    v___x_4792_ = l_Lean_addBuiltinDocString(v___x_4790_, v___x_4791_);
    return v___x_4792_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(
    mut v_a_4793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4794_: *mut LeanObject = core::ptr::null_mut();
    v_res_4794_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
    return v_res_4794_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    v___x_4821_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
    v___x_4822_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6;
    v___x_4823_ = l_Lean_addBuiltinDeclarationRanges(v___x_4821_, v___x_4822_);
    return v___x_4823_;
}
pub unsafe fn l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(
    mut v_a_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4825_: *mut LeanObject = core::ptr::null_mut();
    v_res_4825_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
    return v_res_4825_;
}
pub unsafe fn _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2() -> *mut LeanObject {
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    v___x_4829_ = lean_box(0);
    v___x_4830_ = lean_unsigned_to_nat(3);
    v___x_4831_ = lean_mk_empty_array_with_capacity(v___x_4830_);
    v___x_4832_ = lean_array_push(v___x_4831_, v___x_4829_);
    return v___x_4832_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
    mut v_expectedType_4833_: *mut LeanObject,
    mut v_e_4834_: *mut LeanObject,
    mut v_a_4835_: *mut LeanObject,
    mut v_a_4836_: *mut LeanObject,
    mut v_a_4837_: *mut LeanObject,
    mut v_a_4838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    v___x_4840_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__1;
    v___x_4841_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4841_, 0, v_expectedType_4833_);
    v___x_4842_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4842_, 0, v_e_4834_);
    v___x_4843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2_once),
        _init_l_Lean_Elab_ComputedFields_mkUnsafeCastTo___closed__2,
    );
    v___x_4844_ = lean_array_push(v___x_4843_, v___x_4841_);
    v___x_4845_ = lean_array_push(v___x_4844_, v___x_4842_);
    v___x_4846_ = l_Lean_Meta_mkAppOptM(
        v___x_4840_,
        v___x_4845_,
        v_a_4835_,
        v_a_4836_,
        v_a_4837_,
        v_a_4838_,
    );
    return v___x_4846_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkUnsafeCastTo___boxed(
    mut v_expectedType_4847_: *mut LeanObject,
    mut v_e_4848_: *mut LeanObject,
    mut v_a_4849_: *mut LeanObject,
    mut v_a_4850_: *mut LeanObject,
    mut v_a_4851_: *mut LeanObject,
    mut v_a_4852_: *mut LeanObject,
    mut v_a_4853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4854_: *mut LeanObject = core::ptr::null_mut();
    v_res_4854_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
        v_expectedType_4847_,
        v_e_4848_,
        v_a_4849_,
        v_a_4850_,
        v_a_4851_,
        v_a_4852_,
    );
    lean_dec(v_a_4852_);
    lean_dec_ref(v_a_4851_);
    lean_dec(v_a_4850_);
    lean_dec_ref(v_a_4849_);
    return v_res_4854_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    v___x_4855_ = l_instMonadEIO(lean_box(0));
    return v___x_4855_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(
    mut v_msg_4858_: *mut LeanObject,
    mut v___y_4859_: *mut LeanObject,
    mut v___y_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v_toFunctor_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___f_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658__overap_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut v_unused_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_unused_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4862_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
                v___x_4863_ = l_StateRefT_x27_instMonad___redArg(v___x_4862_);
                v_toApplicative_4864_ = lean_ctor_get(v___x_4863_, 0);
                v_isSharedCheck_4895_ = (!lean_is_exclusive(v___x_4863_)) as u8;
                if v_isSharedCheck_4895_ == 0 {
                    v_unused_4896_ = lean_ctor_get(v___x_4863_, 1);
                    lean_dec(v_unused_4896_);
                    v___x_4866_ = v___x_4863_;
                    v_isShared_4867_ = v_isSharedCheck_4895_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4864_);
                    lean_dec(v___x_4863_);
                    v___x_4866_ = lean_box(0);
                    v_isShared_4867_ = v_isSharedCheck_4895_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4868_ = lean_ctor_get(v_toApplicative_4864_, 0);
                v_toSeq_4869_ = lean_ctor_get(v_toApplicative_4864_, 2);
                v_toSeqLeft_4870_ = lean_ctor_get(v_toApplicative_4864_, 3);
                v_toSeqRight_4871_ = lean_ctor_get(v_toApplicative_4864_, 4);
                v_isSharedCheck_4893_ = (!lean_is_exclusive(v_toApplicative_4864_)) as u8;
                if v_isSharedCheck_4893_ == 0 {
                    v_unused_4894_ = lean_ctor_get(v_toApplicative_4864_, 1);
                    lean_dec(v_unused_4894_);
                    v___x_4873_ = v_toApplicative_4864_;
                    v_isShared_4874_ = v_isSharedCheck_4893_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4871_);
                    lean_inc(v_toSeqLeft_4870_);
                    lean_inc(v_toSeq_4869_);
                    lean_inc(v_toFunctor_4868_);
                    lean_dec(v_toApplicative_4864_);
                    v___x_4873_ = lean_box(0);
                    v_isShared_4874_ = v_isSharedCheck_4893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4875_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1;
                v___f_4876_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_4868_);
                v___f_4877_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4877_, 0, v_toFunctor_4868_);
                v___f_4878_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4878_, 0, v_toFunctor_4868_);
                v___x_4879_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4879_, 0, v___f_4877_);
                lean_ctor_set(v___x_4879_, 1, v___f_4878_);
                v___f_4880_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4880_, 0, v_toSeqRight_4871_);
                v___f_4881_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4881_, 0, v_toSeqLeft_4870_);
                v___f_4882_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4882_, 0, v_toSeq_4869_);
                if v_isShared_4874_ == 0 {
                    lean_ctor_set(v___x_4873_, 4, v___f_4880_);
                    lean_ctor_set(v___x_4873_, 3, v___f_4881_);
                    lean_ctor_set(v___x_4873_, 2, v___f_4882_);
                    lean_ctor_set(v___x_4873_, 1, v___f_4875_);
                    lean_ctor_set(v___x_4873_, 0, v___x_4879_);
                    v___x_4884_ = v___x_4873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4879_);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 1, v___f_4875_);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 2, v___f_4882_);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 3, v___f_4881_);
                    lean_ctor_set(v_reuseFailAlloc_4892_, 4, v___f_4880_);
                    v___x_4884_ = v_reuseFailAlloc_4892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4867_ == 0 {
                    lean_ctor_set(v___x_4866_, 1, v___f_4876_);
                    lean_ctor_set(v___x_4866_, 0, v___x_4884_);
                    v___x_4886_ = v___x_4866_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4884_);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 1, v___f_4876_);
                    v___x_4886_ = v_reuseFailAlloc_4891_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4887_ = lean_box(0);
                v___x_4888_ = l_instInhabitedOfMonad___redArg(v___x_4886_, v___x_4887_);
                v___x_658__overap_4889_ = lean_panic_fn_borrowed(v___x_4888_, v_msg_4858_);
                lean_dec(v___x_4888_);
                lean_inc(v___y_4860_);
                lean_inc_ref(v___y_4859_);
                v___x_4890_ = lean_apply_3(
                    v___x_658__overap_4889_,
                    v___y_4859_,
                    v___y_4860_,
                    lean_box(0),
                );
                return v___x_4890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___boxed(
    mut v_msg_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4901_: *mut LeanObject = core::ptr::null_mut();
    v_res_4901_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v_msg_4897_, v___y_4898_, v___y_4899_);
    lean_dec(v___y_4899_);
    lean_dec_ref(v___y_4898_);
    return v_res_4901_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    v___x_4903_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__0;
    v___x_4904_ = l_Lean_stringToMessageData(v___x_4903_);
    return v___x_4904_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    v___x_4906_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__2;
    v___x_4907_ = l_Lean_stringToMessageData(v___x_4906_);
    return v___x_4907_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    v___x_4911_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6;
    v___x_4912_ = lean_unsigned_to_nat(11);
    v___x_4913_ = lean_unsigned_to_nat(122);
    v___x_4914_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__5;
    v___x_4915_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4;
    v___x_4916_ = l_mkPanicMessageWithDecl(
        v___x_4915_,
        v___x_4914_,
        v___x_4913_,
        v___x_4912_,
        v___x_4911_,
    );
    return v___x_4916_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(
    mut v_constName_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
    mut v___y_4919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: u8 = 0;
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: u8 = 0;
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4934_: u8 = 0;
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v_val_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4954_: u8 = 0;
    let mut v_a_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4958_: u8 = 0;
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4929_ = lean_st_ref_get(v___y_4919_);
                v_env_4930_ = lean_ctor_get(v___x_4929_, 0);
                lean_inc_ref(v_env_4930_);
                lean_dec(v___x_4929_);
                v___x_4931_ = 0;
                lean_inc(v_constName_4917_);
                v___x_4932_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4930_, v_constName_4917_, v___x_4931_);
                if lean_obj_tag(v___x_4932_) == 1 {
                    v_val_4933_ = lean_ctor_get(v___x_4932_, 0);
                    lean_inc(v_val_4933_);
                    lean_dec_ref_known(v___x_4932_, 1);
                    v_kind_4934_ = lean_ctor_get_uint8(
                        v_val_4933_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_4934_ == 6 {
                        v___x_4935_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4933_);
                        if lean_obj_tag(v___x_4935_) == 6 {
                            lean_dec(v_constName_4917_);
                            v_val_4936_ = lean_ctor_get(v___x_4935_, 0);
                            v_isSharedCheck_4943_ = (!lean_is_exclusive(v___x_4935_)) as u8;
                            if v_isSharedCheck_4943_ == 0 {
                                v___x_4938_ = v___x_4935_;
                                v_isShared_4939_ = v_isSharedCheck_4943_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_4936_);
                                lean_dec(v___x_4935_);
                                v___x_4938_ = lean_box(0);
                                v_isShared_4939_ = v_isSharedCheck_4943_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4935_);
                            v___x_4944_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
                            v___x_4945_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(v___x_4944_, v___y_4918_, v___y_4919_);
                            if lean_obj_tag(v___x_4945_) == 0 {
                                v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
                                v_isSharedCheck_4954_ = (!lean_is_exclusive(v___x_4945_)) as u8;
                                if v_isSharedCheck_4954_ == 0 {
                                    v___x_4948_ = v___x_4945_;
                                    v_isShared_4949_ = v_isSharedCheck_4954_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4946_);
                                    lean_dec(v___x_4945_);
                                    v___x_4948_ = lean_box(0);
                                    v_isShared_4949_ = v_isSharedCheck_4954_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_4917_);
                                v_a_4955_ = lean_ctor_get(v___x_4945_, 0);
                                v_isSharedCheck_4962_ = (!lean_is_exclusive(v___x_4945_)) as u8;
                                if v_isSharedCheck_4962_ == 0 {
                                    v___x_4957_ = v___x_4945_;
                                    v_isShared_4958_ = v_isSharedCheck_4962_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4955_);
                                    lean_dec(v___x_4945_);
                                    v___x_4957_ = lean_box(0);
                                    v_isShared_4958_ = v_isSharedCheck_4962_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_4933_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4932_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4922_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
                v___x_4923_ = 0;
                v___x_4924_ = l_Lean_MessageData_ofConstName(v_constName_4917_, v___x_4923_);
                v___x_4925_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4925_, 0, v___x_4922_);
                lean_ctor_set(v___x_4925_, 1, v___x_4924_);
                v___x_4926_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
                v___x_4927_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4927_, 0, v___x_4925_);
                lean_ctor_set(v___x_4927_, 1, v___x_4926_);
                v___x_4928_ = l_Lean_throwError___at___00__private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_4927_, v___y_4918_, v___y_4919_);
                return v___x_4928_;
            }
            2 => {
                if v_isShared_4939_ == 0 {
                    lean_ctor_set_tag(v___x_4938_, 0);
                    v___x_4941_ = v___x_4938_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_val_4936_);
                    v___x_4941_ = v_reuseFailAlloc_4942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4941_;
            }
            4 => {
                if lean_obj_tag(v_a_4946_) == 0 {
                    lean_del_object(v___x_4948_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_4917_);
                    v_val_4950_ = lean_ctor_get(v_a_4946_, 0);
                    lean_inc(v_val_4950_);
                    lean_dec_ref_known(v_a_4946_, 1);
                    if v_isShared_4949_ == 0 {
                        lean_ctor_set(v___x_4948_, 0, v_val_4950_);
                        v___x_4952_ = v___x_4948_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_val_4950_);
                        v___x_4952_ = v_reuseFailAlloc_4953_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4952_;
            }
            6 => {
                if v_isShared_4958_ == 0 {
                    v___x_4960_ = v___x_4957_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
                    v___x_4960_ = v_reuseFailAlloc_4961_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(
    mut v_constName_4963_: *mut LeanObject,
    mut v___y_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4967_: *mut LeanObject = core::ptr::null_mut();
    v_res_4967_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(
        v_constName_4963_,
        v___y_4964_,
        v___y_4965_,
    );
    lean_dec(v___y_4965_);
    lean_dec_ref(v___y_4964_);
    return v_res_4967_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_isScalarField(
    mut v_ctor_4968_: *mut LeanObject,
    mut v_a_4969_: *mut LeanObject,
    mut v_a_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v_numFields_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: u8 = 0;
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_a_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4972_ =
                    l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(
                        v_ctor_4968_,
                        v_a_4969_,
                        v_a_4970_,
                    );
                if lean_obj_tag(v___x_4972_) == 0 {
                    v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
                    v_isSharedCheck_4984_ = (!lean_is_exclusive(v___x_4972_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4975_ = v___x_4972_;
                        v_isShared_4976_ = v_isSharedCheck_4984_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4973_);
                        lean_dec(v___x_4972_);
                        v___x_4975_ = lean_box(0);
                        v_isShared_4976_ = v_isSharedCheck_4984_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4985_ = lean_ctor_get(v___x_4972_, 0);
                    v_isSharedCheck_4992_ = (!lean_is_exclusive(v___x_4972_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4987_ = v___x_4972_;
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4985_);
                        lean_dec(v___x_4972_);
                        v___x_4987_ = lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_numFields_4977_ = lean_ctor_get(v_a_4973_, 4);
                lean_inc(v_numFields_4977_);
                lean_dec(v_a_4973_);
                v___x_4978_ = lean_unsigned_to_nat(0);
                v___x_4979_ = lean_nat_dec_eq(v_numFields_4977_, v___x_4978_);
                lean_dec(v_numFields_4977_);
                v___x_4980_ = lean_box((v___x_4979_) as usize);
                if v_isShared_4976_ == 0 {
                    lean_ctor_set(v___x_4975_, 0, v___x_4980_);
                    v___x_4982_ = v___x_4975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4983_, 0, v___x_4980_);
                    v___x_4982_ = v_reuseFailAlloc_4983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4982_;
            }
            3 => {
                if v_isShared_4988_ == 0 {
                    v___x_4990_ = v___x_4987_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
                    v___x_4990_ = v_reuseFailAlloc_4991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_isScalarField___boxed(
    mut v_ctor_4993_: *mut LeanObject,
    mut v_a_4994_: *mut LeanObject,
    mut v_a_4995_: *mut LeanObject,
    mut v_a_4996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4997_: *mut LeanObject = core::ptr::null_mut();
    v_res_4997_ = l_Lean_Elab_ComputedFields_isScalarField(v_ctor_4993_, v_a_4994_, v_a_4995_);
    lean_dec(v_a_4995_);
    lean_dec_ref(v_a_4994_);
    return v_res_4997_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(
    mut v_msgData_4998_: *mut LeanObject,
    mut v___y_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    v___x_5004_ = lean_st_ref_get(v___y_5002_);
    v_env_5005_ = lean_ctor_get(v___x_5004_, 0);
    lean_inc_ref(v_env_5005_);
    lean_dec(v___x_5004_);
    v___x_5006_ = lean_st_ref_get(v___y_5000_);
    v_mctx_5007_ = lean_ctor_get(v___x_5006_, 0);
    lean_inc_ref(v_mctx_5007_);
    lean_dec(v___x_5006_);
    v_lctx_5008_ = lean_ctor_get(v___y_4999_, 2);
    v_options_5009_ = lean_ctor_get(v___y_5001_, 2);
    lean_inc_ref(v_options_5009_);
    lean_inc_ref(v_lctx_5008_);
    v___x_5010_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_5010_, 0, v_env_5005_);
    lean_ctor_set(v___x_5010_, 1, v_mctx_5007_);
    lean_ctor_set(v___x_5010_, 2, v_lctx_5008_);
    lean_ctor_set(v___x_5010_, 3, v_options_5009_);
    v___x_5011_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_5011_, 0, v___x_5010_);
    lean_ctor_set(v___x_5011_, 1, v_msgData_4998_);
    v___x_5012_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5012_, 0, v___x_5011_);
    return v___x_5012_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2___boxed(
    mut v_msgData_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
    mut v___y_5015_: *mut LeanObject,
    mut v___y_5016_: *mut LeanObject,
    mut v___y_5017_: *mut LeanObject,
    mut v___y_5018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5019_: *mut LeanObject = core::ptr::null_mut();
    v_res_5019_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msgData_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
    lean_dec(v___y_5017_);
    lean_dec_ref(v___y_5016_);
    lean_dec(v___y_5015_);
    lean_dec_ref(v___y_5014_);
    return v_res_5019_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(
    mut v_msg_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5031_: u8 = 0;
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5026_ = lean_ctor_get(v___y_5023_, 5);
                v___x_5027_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
                v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
                v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_5027_)) as u8;
                if v_isSharedCheck_5036_ == 0 {
                    v___x_5030_ = v___x_5027_;
                    v_isShared_5031_ = v_isSharedCheck_5036_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5028_);
                    lean_dec(v___x_5027_);
                    v___x_5030_ = lean_box(0);
                    v_isShared_5031_ = v_isSharedCheck_5036_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5026_);
                v___x_5032_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5032_, 0, v_ref_5026_);
                lean_ctor_set(v___x_5032_, 1, v_a_5028_);
                if v_isShared_5031_ == 0 {
                    lean_ctor_set_tag(v___x_5030_, 1);
                    lean_ctor_set(v___x_5030_, 0, v___x_5032_);
                    v___x_5034_ = v___x_5030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg___boxed(
    mut v_msg_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5043_: *mut LeanObject = core::ptr::null_mut();
    v_res_5043_ =
        l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(
            v_msg_5037_,
            v___y_5038_,
            v___y_5039_,
            v___y_5040_,
            v___y_5041_,
        );
    lean_dec(v___y_5041_);
    lean_dec_ref(v___y_5040_);
    lean_dec(v___y_5039_);
    lean_dec_ref(v___y_5038_);
    return v_res_5043_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(
    mut v_k_5044_: *mut LeanObject,
    mut v_t_5045_: *mut LeanObject,
) -> u8 {
    let mut v_k_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: u8 = 0;
    let mut v___x_5051_: u8 = 0;
    let mut v___x_5053_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5045_) == 0 {
                    v_k_5046_ = lean_ctor_get(v_t_5045_, 1);
                    v_l_5047_ = lean_ctor_get(v_t_5045_, 3);
                    v_r_5048_ = lean_ctor_get(v_t_5045_, 4);
                    v___x_5049_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5044_, v_k_5046_);
                    match v___x_5049_ {
                        0 => {
                            v_t_5045_ = v_l_5047_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_5051_ = 1;
                            return v___x_5051_;
                        }
                        _ => {
                            v_t_5045_ = v_r_5048_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5053_ = 0;
                    return v___x_5053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_k_5054_: *mut LeanObject,
    mut v_t_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5056_: u8 = 0;
    let mut v_r_5057_: *mut LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_5054_, v_t_5055_);
    lean_dec(v_t_5055_);
    lean_dec(v_k_5054_);
    v_r_5057_ = lean_box((v_res_5056_) as usize);
    return v_r_5057_;
}
pub unsafe fn l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(
    mut v_msg_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983__overap_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    v___f_5065_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0;
    v___x_3983__overap_5066_ = lean_panic_fn_borrowed(v___f_5065_, v_msg_5059_);
    lean_inc(v___y_5063_);
    lean_inc_ref(v___y_5062_);
    lean_inc(v___y_5061_);
    lean_inc_ref(v___y_5060_);
    v___x_5067_ = lean_apply_5(
        v___x_3983__overap_5066_,
        v___y_5060_,
        v___y_5061_,
        v___y_5062_,
        v___y_5063_,
        lean_box(0),
    );
    return v___x_5067_;
}
pub unsafe fn l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(
    mut v_msg_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5074_: *mut LeanObject = core::ptr::null_mut();
    v_res_5074_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
    lean_dec(v___y_5072_);
    lean_dec_ref(v___y_5071_);
    lean_dec(v___y_5070_);
    lean_dec_ref(v___y_5069_);
    return v_res_5074_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(
    mut v_mvarId_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5078_ = lean_st_ref_get(v___y_5076_);
    v_mctx_5079_ = lean_ctor_get(v___x_5078_, 0);
    lean_inc_ref(v_mctx_5079_);
    lean_dec(v___x_5078_);
    v___x_5080_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_5079_, v_mvarId_5075_);
    lean_dec_ref(v_mctx_5079_);
    v___x_5081_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5081_, 0, v___x_5080_);
    return v___x_5081_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_mvarId_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5085_: *mut LeanObject = core::ptr::null_mut();
    v_res_5085_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_5082_, v___y_5083_);
    lean_dec(v___y_5083_);
    lean_dec(v_mvarId_5082_);
    return v_res_5085_;
}
pub unsafe fn _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    v___x_5089_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__2;
    v___x_5090_ = lean_unsigned_to_nat(22);
    v___x_5091_ = lean_unsigned_to_nat(391);
    v___x_5092_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__1;
    v___x_5093_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__0;
    v___x_5094_ = l_mkPanicMessageWithDecl(
        v___x_5093_,
        v___x_5092_,
        v___x_5091_,
        v___x_5090_,
        v___x_5089_,
    );
    return v___x_5094_;
}
pub unsafe fn l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(
    mut v_ctorTerm_5095_: *mut LeanObject,
    mut v_e_5096_: *mut LeanObject,
    mut v_a_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
    mut v_a_5099_: *mut LeanObject,
    mut v_a_5100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v_value_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_5111_: u8 = 0;
    let mut v___y_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5114_: u8 = 0;
    let mut v___y_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5128_: u8 = 0;
    let mut v___y_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5134_: u8 = 0;
    let mut v___x_5135_: u8 = 0;
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDelta_5137_: u8 = 0;
    let mut v_trackZetaDelta_5138_: u8 = 0;
    let mut v_zetaDeltaSet_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_a_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5154_: u8 = 0;
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5158_: u8 = 0;
    let mut v_mvarId_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut v_a_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5174_: u8 = 0;
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: u8 = 0;
    let mut v___x_5188_: u8 = 0;
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5193_: u8 = 0;
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5199_: u8 = 0;
    let mut v_a_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5203_: u8 = 0;
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_5096_) {
                0 => {
                    lean_dec_ref_known(v_e_5096_, 1);
                    lean_dec_ref(v_ctorTerm_5095_);
                    v___x_5102_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once), _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
                    v___x_5103_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_5102_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_);
                    return v___x_5103_;
                }
                1 => {
                    v_fvarId_5104_ = lean_ctor_get(v_e_5096_, 0);
                    lean_inc(v_fvarId_5104_);
                    v___x_5105_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_5104_,
                        v_a_5097_,
                        v_a_5099_,
                        v_a_5100_,
                    );
                    if lean_obj_tag(v___x_5105_) == 0 {
                        v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
                        v_isSharedCheck_5150_ = (!lean_is_exclusive(v___x_5105_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5108_ = v___x_5105_;
                            v_isShared_5109_ = v_isSharedCheck_5150_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5106_);
                            lean_dec(v___x_5105_);
                            v___x_5108_ = lean_box(0);
                            v_isShared_5109_ = v_isSharedCheck_5150_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_e_5096_, 1);
                        lean_dec_ref(v_ctorTerm_5095_);
                        v_a_5151_ = lean_ctor_get(v___x_5105_, 0);
                        v_isSharedCheck_5158_ = (!lean_is_exclusive(v___x_5105_)) as u8;
                        if v_isSharedCheck_5158_ == 0 {
                            v___x_5153_ = v___x_5105_;
                            v_isShared_5154_ = v_isSharedCheck_5158_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5151_);
                            lean_dec(v___x_5105_);
                            v___x_5153_ = lean_box(0);
                            v_isShared_5154_ = v_isSharedCheck_5158_;
                            state = 9;
                            continue;
                        }
                    }
                }
                2 => {
                    v_mvarId_5159_ = lean_ctor_get(v_e_5096_, 0);
                    v___x_5160_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_5159_, v_a_5098_);
                    if lean_obj_tag(v___x_5160_) == 0 {
                        v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
                        v_isSharedCheck_5170_ = (!lean_is_exclusive(v___x_5160_)) as u8;
                        if v_isSharedCheck_5170_ == 0 {
                            v___x_5163_ = v___x_5160_;
                            v_isShared_5164_ = v_isSharedCheck_5170_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_5161_);
                            lean_dec(v___x_5160_);
                            v___x_5163_ = lean_box(0);
                            v_isShared_5164_ = v_isSharedCheck_5170_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_e_5096_, 1);
                        lean_dec_ref(v_ctorTerm_5095_);
                        v_a_5171_ = lean_ctor_get(v___x_5160_, 0);
                        v_isSharedCheck_5178_ = (!lean_is_exclusive(v___x_5160_)) as u8;
                        if v_isSharedCheck_5178_ == 0 {
                            v___x_5173_ = v___x_5160_;
                            v_isShared_5174_ = v_isSharedCheck_5178_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5171_);
                            lean_dec(v___x_5160_);
                            v___x_5173_ = lean_box(0);
                            v_isShared_5174_ = v_isSharedCheck_5178_;
                            state = 13;
                            continue;
                        }
                    }
                }
                3 => {
                    lean_dec_ref(v_ctorTerm_5095_);
                    v___x_5179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5179_, 0, v_e_5096_);
                    return v___x_5179_;
                }
                6 => {
                    lean_dec_ref(v_ctorTerm_5095_);
                    v___x_5180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5180_, 0, v_e_5096_);
                    return v___x_5180_;
                }
                7 => {
                    lean_dec_ref(v_ctorTerm_5095_);
                    v___x_5181_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5181_, 0, v_e_5096_);
                    return v___x_5181_;
                }
                9 => {
                    lean_dec_ref(v_ctorTerm_5095_);
                    v___x_5182_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5182_, 0, v_e_5096_);
                    return v___x_5182_;
                }
                10 => {
                    v_expr_5183_ = lean_ctor_get(v_e_5096_, 1);
                    lean_inc_ref(v_expr_5183_);
                    lean_dec_ref_known(v_e_5096_, 2);
                    v_e_5096_ = v_expr_5183_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_5185_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(
                        v_e_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_,
                    );
                    if lean_obj_tag(v___x_5185_) == 0 {
                        v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
                        lean_inc(v_a_5186_);
                        lean_inc_ref(v_ctorTerm_5095_);
                        v___x_5187_ = l_Lean_Expr_occurs(v_ctorTerm_5095_, v_a_5186_);
                        if v___x_5187_ == 0 {
                            lean_dec(v_a_5186_);
                            lean_dec_ref(v_ctorTerm_5095_);
                            return v___x_5185_;
                        } else {
                            lean_dec_ref_known(v___x_5185_, 1);
                            v___x_5188_ = 0;
                            lean_inc(v_a_5186_);
                            v___x_5189_ = l_Lean_Meta_unfoldDefinition_x3f(
                                v_a_5186_,
                                v___x_5188_,
                                v_a_5097_,
                                v_a_5098_,
                                v_a_5099_,
                                v_a_5100_,
                            );
                            if lean_obj_tag(v___x_5189_) == 0 {
                                v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
                                v_isSharedCheck_5199_ = (!lean_is_exclusive(v___x_5189_)) as u8;
                                if v_isSharedCheck_5199_ == 0 {
                                    v___x_5192_ = v___x_5189_;
                                    v_isShared_5193_ = v_isSharedCheck_5199_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_5190_);
                                    lean_dec(v___x_5189_);
                                    v___x_5192_ = lean_box(0);
                                    v_isShared_5193_ = v_isSharedCheck_5199_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5186_);
                                lean_dec_ref(v_ctorTerm_5095_);
                                v_a_5200_ = lean_ctor_get(v___x_5189_, 0);
                                v_isSharedCheck_5207_ = (!lean_is_exclusive(v___x_5189_)) as u8;
                                if v_isSharedCheck_5207_ == 0 {
                                    v___x_5202_ = v___x_5189_;
                                    v_isShared_5203_ = v_isSharedCheck_5207_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_5200_);
                                    lean_dec(v___x_5189_);
                                    v___x_5202_ = lean_box(0);
                                    v_isShared_5203_ = v_isSharedCheck_5207_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_ctorTerm_5095_);
                        return v___x_5185_;
                    }
                }
            },
            1 => {
                if lean_obj_tag(v_a_5106_) == 1 {
                    v_value_5110_ = lean_ctor_get(v_a_5106_, 4);
                    lean_inc_ref(v_value_5110_);
                    v_nondep_5111_ = lean_ctor_get_uint8(
                        v_a_5106_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    if v_nondep_5111_ == 0 {
                        v___x_5135_ = l_Lean_LocalDecl_isImplementationDetail(v_a_5106_);
                        lean_dec_ref_known(v_a_5106_, 5);
                        if v___x_5135_ == 0 {
                            v___x_5136_ = l_Lean_Meta_Context_config(v_a_5097_);
                            v_zetaDelta_5137_ = lean_ctor_get_uint8(v___x_5136_, 16 as u32);
                            lean_dec_ref(v___x_5136_);
                            if v_zetaDelta_5137_ == 0 {
                                v_trackZetaDelta_5138_ = lean_ctor_get_uint8(
                                    v_a_5097_,
                                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                                );
                                v_zetaDeltaSet_5139_ = lean_ctor_get(v_a_5097_, 1);
                                v___x_5140_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_5104_, v_zetaDeltaSet_5139_);
                                if v___x_5140_ == 0 {
                                    lean_dec_ref(v_value_5110_);
                                    lean_dec_ref(v_ctorTerm_5095_);
                                    if v_isShared_5109_ == 0 {
                                        lean_ctor_set(v___x_5108_, 0, v_e_5096_);
                                        v___x_5142_ = v___x_5108_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_e_5096_);
                                        v___x_5142_ = v_reuseFailAlloc_5143_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_fvarId_5104_);
                                    lean_del_object(v___x_5108_);
                                    lean_dec_ref_known(v_e_5096_, 1);
                                    v___y_5113_ = v_a_5097_;
                                    v_trackZetaDelta_5114_ = v_trackZetaDelta_5138_;
                                    v___y_5115_ = v_a_5098_;
                                    v___y_5116_ = v_a_5099_;
                                    v___y_5117_ = v_a_5100_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_inc(v_fvarId_5104_);
                                lean_del_object(v___x_5108_);
                                lean_dec_ref_known(v_e_5096_, 1);
                                v___y_5130_ = v_a_5097_;
                                v___y_5131_ = v_a_5098_;
                                v___y_5132_ = v_a_5099_;
                                v___y_5133_ = v_a_5100_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_inc(v_fvarId_5104_);
                            lean_del_object(v___x_5108_);
                            lean_dec_ref_known(v_e_5096_, 1);
                            v___y_5130_ = v_a_5097_;
                            v___y_5131_ = v_a_5098_;
                            v___y_5132_ = v_a_5099_;
                            v___y_5133_ = v_a_5100_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_value_5110_);
                        lean_dec_ref_known(v_a_5106_, 5);
                        lean_dec_ref(v_ctorTerm_5095_);
                        if v_isShared_5109_ == 0 {
                            lean_ctor_set(v___x_5108_, 0, v_e_5096_);
                            v___x_5145_ = v___x_5108_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_e_5096_);
                            v___x_5145_ = v_reuseFailAlloc_5146_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5106_);
                    lean_dec_ref(v_ctorTerm_5095_);
                    if v_isShared_5109_ == 0 {
                        lean_ctor_set(v___x_5108_, 0, v_e_5096_);
                        v___x_5148_ = v___x_5108_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_e_5096_);
                        v___x_5148_ = v_reuseFailAlloc_5149_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_trackZetaDelta_5114_ == 0 {
                    lean_dec(v_fvarId_5104_);
                    v_e_5096_ = v_value_5110_;
                    v_a_5097_ = v___y_5113_;
                    v_a_5098_ = v___y_5115_;
                    v_a_5099_ = v___y_5116_;
                    v_a_5100_ = v___y_5117_;
                    state = 0;
                    continue;
                } else {
                    v___x_5119_ =
                        l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_5104_, v___y_5115_);
                    if lean_obj_tag(v___x_5119_) == 0 {
                        lean_dec_ref_known(v___x_5119_, 1);
                        v_e_5096_ = v_value_5110_;
                        v_a_5097_ = v___y_5113_;
                        v_a_5098_ = v___y_5115_;
                        v_a_5099_ = v___y_5116_;
                        v_a_5100_ = v___y_5117_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_value_5110_);
                        lean_dec_ref(v_ctorTerm_5095_);
                        v_a_5121_ = lean_ctor_get(v___x_5119_, 0);
                        v_isSharedCheck_5128_ = (!lean_is_exclusive(v___x_5119_)) as u8;
                        if v_isSharedCheck_5128_ == 0 {
                            v___x_5123_ = v___x_5119_;
                            v_isShared_5124_ = v_isSharedCheck_5128_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5121_);
                            lean_dec(v___x_5119_);
                            v___x_5123_ = lean_box(0);
                            v_isShared_5124_ = v_isSharedCheck_5128_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_5124_ == 0 {
                    v___x_5126_ = v___x_5123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
                    v___x_5126_ = v_reuseFailAlloc_5127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5126_;
            }
            5 => {
                v_trackZetaDelta_5134_ = lean_ctor_get_uint8(
                    v___y_5130_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v___y_5113_ = v___y_5130_;
                v_trackZetaDelta_5114_ = v_trackZetaDelta_5134_;
                v___y_5115_ = v___y_5131_;
                v___y_5116_ = v___y_5132_;
                v___y_5117_ = v___y_5133_;
                state = 2;
                continue;
            }
            6 => {
                return v___x_5142_;
            }
            7 => {
                return v___x_5145_;
            }
            8 => {
                return v___x_5148_;
            }
            9 => {
                if v_isShared_5154_ == 0 {
                    v___x_5156_ = v___x_5153_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
                    v___x_5156_ = v_reuseFailAlloc_5157_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5156_;
            }
            11 => {
                if lean_obj_tag(v_a_5161_) == 0 {
                    lean_dec_ref(v_ctorTerm_5095_);
                    if v_isShared_5164_ == 0 {
                        lean_ctor_set(v___x_5163_, 0, v_e_5096_);
                        v___x_5166_ = v___x_5163_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_e_5096_);
                        v___x_5166_ = v_reuseFailAlloc_5167_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5163_);
                    lean_dec_ref_known(v_e_5096_, 1);
                    v_val_5168_ = lean_ctor_get(v_a_5161_, 0);
                    lean_inc(v_val_5168_);
                    lean_dec_ref_known(v_a_5161_, 1);
                    v_e_5096_ = v_val_5168_;
                    state = 0;
                    continue;
                }
            }
            12 => {
                return v___x_5166_;
            }
            13 => {
                if v_isShared_5174_ == 0 {
                    v___x_5176_ = v___x_5173_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
                    v___x_5176_ = v_reuseFailAlloc_5177_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5176_;
            }
            15 => {
                if lean_obj_tag(v_a_5190_) == 0 {
                    lean_dec_ref(v_ctorTerm_5095_);
                    if v_isShared_5193_ == 0 {
                        lean_ctor_set(v___x_5192_, 0, v_a_5186_);
                        v___x_5195_ = v___x_5192_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5196_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5186_);
                        v___x_5195_ = v_reuseFailAlloc_5196_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5192_);
                    lean_dec(v_a_5186_);
                    v_val_5197_ = lean_ctor_get(v_a_5190_, 0);
                    lean_inc(v_val_5197_);
                    lean_dec_ref_known(v_a_5190_, 1);
                    v___x_5198_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_5095_, v_val_5197_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_);
                    return v___x_5198_;
                }
            }
            16 => {
                return v___x_5195_;
            }
            17 => {
                if v_isShared_5203_ == 0 {
                    v___x_5205_ = v___x_5202_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
                    v___x_5205_ = v_reuseFailAlloc_5206_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(
    mut v_ctorTerm_5208_: *mut LeanObject,
    mut v_e_5209_: *mut LeanObject,
    mut v_a_5210_: *mut LeanObject,
    mut v_a_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5222_: u8 = 0;
    let mut v_value_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_5224_: u8 = 0;
    let mut v___y_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5227_: u8 = 0;
    let mut v___y_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5237_: u8 = 0;
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5241_: u8 = 0;
    let mut v___y_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5247_: u8 = 0;
    let mut v___x_5248_: u8 = 0;
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDelta_5250_: u8 = 0;
    let mut v_trackZetaDelta_5251_: u8 = 0;
    let mut v_zetaDeltaSet_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: u8 = 0;
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut v_a_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5267_: u8 = 0;
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5271_: u8 = 0;
    let mut v_mvarId_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_a_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5287_: u8 = 0;
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: u8 = 0;
    let mut v___x_5301_: u8 = 0;
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
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
            0 => match lean_obj_tag(v_e_5209_) {
                0 => {
                    lean_dec_ref_known(v_e_5209_, 1);
                    lean_dec_ref(v_ctorTerm_5208_);
                    v___x_5215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once), _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
                    v___x_5216_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_5215_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_);
                    return v___x_5216_;
                }
                1 => {
                    v_fvarId_5217_ = lean_ctor_get(v_e_5209_, 0);
                    lean_inc(v_fvarId_5217_);
                    v___x_5218_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_5217_,
                        v_a_5210_,
                        v_a_5212_,
                        v_a_5213_,
                    );
                    if lean_obj_tag(v___x_5218_) == 0 {
                        v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
                        v_isSharedCheck_5263_ = (!lean_is_exclusive(v___x_5218_)) as u8;
                        if v_isSharedCheck_5263_ == 0 {
                            v___x_5221_ = v___x_5218_;
                            v_isShared_5222_ = v_isSharedCheck_5263_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5219_);
                            lean_dec(v___x_5218_);
                            v___x_5221_ = lean_box(0);
                            v_isShared_5222_ = v_isSharedCheck_5263_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_e_5209_, 1);
                        lean_dec_ref(v_ctorTerm_5208_);
                        v_a_5264_ = lean_ctor_get(v___x_5218_, 0);
                        v_isSharedCheck_5271_ = (!lean_is_exclusive(v___x_5218_)) as u8;
                        if v_isSharedCheck_5271_ == 0 {
                            v___x_5266_ = v___x_5218_;
                            v_isShared_5267_ = v_isSharedCheck_5271_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5264_);
                            lean_dec(v___x_5218_);
                            v___x_5266_ = lean_box(0);
                            v_isShared_5267_ = v_isSharedCheck_5271_;
                            state = 9;
                            continue;
                        }
                    }
                }
                2 => {
                    v_mvarId_5272_ = lean_ctor_get(v_e_5209_, 0);
                    v___x_5273_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_5272_, v_a_5211_);
                    if lean_obj_tag(v___x_5273_) == 0 {
                        v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
                        v_isSharedCheck_5283_ = (!lean_is_exclusive(v___x_5273_)) as u8;
                        if v_isSharedCheck_5283_ == 0 {
                            v___x_5276_ = v___x_5273_;
                            v_isShared_5277_ = v_isSharedCheck_5283_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_5274_);
                            lean_dec(v___x_5273_);
                            v___x_5276_ = lean_box(0);
                            v_isShared_5277_ = v_isSharedCheck_5283_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_e_5209_, 1);
                        lean_dec_ref(v_ctorTerm_5208_);
                        v_a_5284_ = lean_ctor_get(v___x_5273_, 0);
                        v_isSharedCheck_5291_ = (!lean_is_exclusive(v___x_5273_)) as u8;
                        if v_isSharedCheck_5291_ == 0 {
                            v___x_5286_ = v___x_5273_;
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5284_);
                            lean_dec(v___x_5273_);
                            v___x_5286_ = lean_box(0);
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 13;
                            continue;
                        }
                    }
                }
                3 => {
                    lean_dec_ref(v_ctorTerm_5208_);
                    v___x_5292_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5292_, 0, v_e_5209_);
                    return v___x_5292_;
                }
                6 => {
                    lean_dec_ref(v_ctorTerm_5208_);
                    v___x_5293_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5293_, 0, v_e_5209_);
                    return v___x_5293_;
                }
                7 => {
                    lean_dec_ref(v_ctorTerm_5208_);
                    v___x_5294_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5294_, 0, v_e_5209_);
                    return v___x_5294_;
                }
                9 => {
                    lean_dec_ref(v_ctorTerm_5208_);
                    v___x_5295_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5295_, 0, v_e_5209_);
                    return v___x_5295_;
                }
                10 => {
                    v_expr_5296_ = lean_ctor_get(v_e_5209_, 1);
                    lean_inc_ref(v_expr_5296_);
                    lean_dec_ref_known(v_e_5209_, 2);
                    v___x_5297_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_5208_, v_expr_5296_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_);
                    return v___x_5297_;
                }
                _ => {
                    v___x_5298_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(
                        v_e_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_,
                    );
                    if lean_obj_tag(v___x_5298_) == 0 {
                        v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
                        lean_inc(v_a_5299_);
                        lean_inc_ref(v_ctorTerm_5208_);
                        v___x_5300_ = l_Lean_Expr_occurs(v_ctorTerm_5208_, v_a_5299_);
                        if v___x_5300_ == 0 {
                            lean_dec(v_a_5299_);
                            lean_dec_ref(v_ctorTerm_5208_);
                            return v___x_5298_;
                        } else {
                            lean_dec_ref_known(v___x_5298_, 1);
                            v___x_5301_ = 0;
                            lean_inc(v_a_5299_);
                            v___x_5302_ = l_Lean_Meta_unfoldDefinition_x3f(
                                v_a_5299_,
                                v___x_5301_,
                                v_a_5210_,
                                v_a_5211_,
                                v_a_5212_,
                                v_a_5213_,
                            );
                            if lean_obj_tag(v___x_5302_) == 0 {
                                v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
                                v_isSharedCheck_5312_ = (!lean_is_exclusive(v___x_5302_)) as u8;
                                if v_isSharedCheck_5312_ == 0 {
                                    v___x_5305_ = v___x_5302_;
                                    v_isShared_5306_ = v_isSharedCheck_5312_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_5303_);
                                    lean_dec(v___x_5302_);
                                    v___x_5305_ = lean_box(0);
                                    v_isShared_5306_ = v_isSharedCheck_5312_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5299_);
                                lean_dec_ref(v_ctorTerm_5208_);
                                v_a_5313_ = lean_ctor_get(v___x_5302_, 0);
                                v_isSharedCheck_5320_ = (!lean_is_exclusive(v___x_5302_)) as u8;
                                if v_isSharedCheck_5320_ == 0 {
                                    v___x_5315_ = v___x_5302_;
                                    v_isShared_5316_ = v_isSharedCheck_5320_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_5313_);
                                    lean_dec(v___x_5302_);
                                    v___x_5315_ = lean_box(0);
                                    v_isShared_5316_ = v_isSharedCheck_5320_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_ctorTerm_5208_);
                        return v___x_5298_;
                    }
                }
            },
            1 => {
                if lean_obj_tag(v_a_5219_) == 1 {
                    v_value_5223_ = lean_ctor_get(v_a_5219_, 4);
                    lean_inc_ref(v_value_5223_);
                    v_nondep_5224_ = lean_ctor_get_uint8(
                        v_a_5219_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    if v_nondep_5224_ == 0 {
                        v___x_5248_ = l_Lean_LocalDecl_isImplementationDetail(v_a_5219_);
                        lean_dec_ref_known(v_a_5219_, 5);
                        if v___x_5248_ == 0 {
                            v___x_5249_ = l_Lean_Meta_Context_config(v_a_5210_);
                            v_zetaDelta_5250_ = lean_ctor_get_uint8(v___x_5249_, 16 as u32);
                            lean_dec_ref(v___x_5249_);
                            if v_zetaDelta_5250_ == 0 {
                                v_trackZetaDelta_5251_ = lean_ctor_get_uint8(
                                    v_a_5210_,
                                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                                );
                                v_zetaDeltaSet_5252_ = lean_ctor_get(v_a_5210_, 1);
                                v___x_5253_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_5217_, v_zetaDeltaSet_5252_);
                                if v___x_5253_ == 0 {
                                    lean_dec_ref(v_value_5223_);
                                    lean_dec_ref(v_ctorTerm_5208_);
                                    if v_isShared_5222_ == 0 {
                                        lean_ctor_set(v___x_5221_, 0, v_e_5209_);
                                        v___x_5255_ = v___x_5221_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_e_5209_);
                                        v___x_5255_ = v_reuseFailAlloc_5256_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_fvarId_5217_);
                                    lean_del_object(v___x_5221_);
                                    lean_dec_ref_known(v_e_5209_, 1);
                                    v___y_5226_ = v_a_5210_;
                                    v_trackZetaDelta_5227_ = v_trackZetaDelta_5251_;
                                    v___y_5228_ = v_a_5211_;
                                    v___y_5229_ = v_a_5212_;
                                    v___y_5230_ = v_a_5213_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_inc(v_fvarId_5217_);
                                lean_del_object(v___x_5221_);
                                lean_dec_ref_known(v_e_5209_, 1);
                                v___y_5243_ = v_a_5210_;
                                v___y_5244_ = v_a_5211_;
                                v___y_5245_ = v_a_5212_;
                                v___y_5246_ = v_a_5213_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_inc(v_fvarId_5217_);
                            lean_del_object(v___x_5221_);
                            lean_dec_ref_known(v_e_5209_, 1);
                            v___y_5243_ = v_a_5210_;
                            v___y_5244_ = v_a_5211_;
                            v___y_5245_ = v_a_5212_;
                            v___y_5246_ = v_a_5213_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_5219_, 5);
                        lean_dec_ref(v_value_5223_);
                        lean_dec_ref(v_ctorTerm_5208_);
                        if v_isShared_5222_ == 0 {
                            lean_ctor_set(v___x_5221_, 0, v_e_5209_);
                            v___x_5258_ = v___x_5221_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_e_5209_);
                            v___x_5258_ = v_reuseFailAlloc_5259_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5219_);
                    lean_dec_ref(v_ctorTerm_5208_);
                    if v_isShared_5222_ == 0 {
                        lean_ctor_set(v___x_5221_, 0, v_e_5209_);
                        v___x_5261_ = v___x_5221_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_e_5209_);
                        v___x_5261_ = v_reuseFailAlloc_5262_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_trackZetaDelta_5227_ == 0 {
                    lean_dec(v_fvarId_5217_);
                    v___x_5231_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_5208_, v_value_5223_, v___y_5226_, v___y_5228_, v___y_5229_, v___y_5230_);
                    return v___x_5231_;
                } else {
                    v___x_5232_ =
                        l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_5217_, v___y_5228_);
                    if lean_obj_tag(v___x_5232_) == 0 {
                        lean_dec_ref_known(v___x_5232_, 1);
                        v___x_5233_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_5208_, v_value_5223_, v___y_5226_, v___y_5228_, v___y_5229_, v___y_5230_);
                        return v___x_5233_;
                    } else {
                        lean_dec_ref(v_value_5223_);
                        lean_dec_ref(v_ctorTerm_5208_);
                        v_a_5234_ = lean_ctor_get(v___x_5232_, 0);
                        v_isSharedCheck_5241_ = (!lean_is_exclusive(v___x_5232_)) as u8;
                        if v_isSharedCheck_5241_ == 0 {
                            v___x_5236_ = v___x_5232_;
                            v_isShared_5237_ = v_isSharedCheck_5241_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5234_);
                            lean_dec(v___x_5232_);
                            v___x_5236_ = lean_box(0);
                            v_isShared_5237_ = v_isSharedCheck_5241_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_5237_ == 0 {
                    v___x_5239_ = v___x_5236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
                    v___x_5239_ = v_reuseFailAlloc_5240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5239_;
            }
            5 => {
                v_trackZetaDelta_5247_ = lean_ctor_get_uint8(
                    v___y_5243_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v___y_5226_ = v___y_5243_;
                v_trackZetaDelta_5227_ = v_trackZetaDelta_5247_;
                v___y_5228_ = v___y_5244_;
                v___y_5229_ = v___y_5245_;
                v___y_5230_ = v___y_5246_;
                state = 2;
                continue;
            }
            6 => {
                return v___x_5255_;
            }
            7 => {
                return v___x_5258_;
            }
            8 => {
                return v___x_5261_;
            }
            9 => {
                if v_isShared_5267_ == 0 {
                    v___x_5269_ = v___x_5266_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_a_5264_);
                    v___x_5269_ = v_reuseFailAlloc_5270_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5269_;
            }
            11 => {
                if lean_obj_tag(v_a_5274_) == 0 {
                    lean_dec_ref(v_ctorTerm_5208_);
                    if v_isShared_5277_ == 0 {
                        lean_ctor_set(v___x_5276_, 0, v_e_5209_);
                        v___x_5279_ = v___x_5276_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_e_5209_);
                        v___x_5279_ = v_reuseFailAlloc_5280_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5276_);
                    lean_dec_ref_known(v_e_5209_, 1);
                    v_val_5281_ = lean_ctor_get(v_a_5274_, 0);
                    lean_inc(v_val_5281_);
                    lean_dec_ref_known(v_a_5274_, 1);
                    v___x_5282_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_5208_, v_val_5281_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_);
                    return v___x_5282_;
                }
            }
            12 => {
                return v___x_5279_;
            }
            13 => {
                if v_isShared_5287_ == 0 {
                    v___x_5289_ = v___x_5286_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
                    v___x_5289_ = v_reuseFailAlloc_5290_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5289_;
            }
            15 => {
                if lean_obj_tag(v_a_5303_) == 0 {
                    lean_dec_ref(v_ctorTerm_5208_);
                    if v_isShared_5306_ == 0 {
                        lean_ctor_set(v___x_5305_, 0, v_a_5299_);
                        v___x_5308_ = v___x_5305_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5299_);
                        v___x_5308_ = v_reuseFailAlloc_5309_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5305_);
                    lean_dec(v_a_5299_);
                    v_val_5310_ = lean_ctor_get(v_a_5303_, 0);
                    lean_inc(v_val_5310_);
                    lean_dec_ref_known(v_a_5303_, 1);
                    v___x_5311_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_5208_, v_val_5310_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_);
                    return v___x_5311_;
                }
            }
            16 => {
                return v___x_5308_;
            }
            17 => {
                if v_isShared_5316_ == 0 {
                    v___x_5318_ = v___x_5315_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
                    v___x_5318_ = v_reuseFailAlloc_5319_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(
    mut v_ctorTerm_5321_: *mut LeanObject,
    mut v_e_5322_: *mut LeanObject,
    mut v_a_5323_: *mut LeanObject,
    mut v_a_5324_: *mut LeanObject,
    mut v_a_5325_: *mut LeanObject,
    mut v_a_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    v___x_5328_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_5321_, v_e_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_);
    return v___x_5328_;
}
pub unsafe fn l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(
    mut v_ctorTerm_5329_: *mut LeanObject,
    mut v_e_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
    mut v_a_5333_: *mut LeanObject,
    mut v_a_5334_: *mut LeanObject,
    mut v_a_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5336_: *mut LeanObject = core::ptr::null_mut();
    v_res_5336_ =
        l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(
            v_ctorTerm_5329_,
            v_e_5330_,
            v_a_5331_,
            v_a_5332_,
            v_a_5333_,
            v_a_5334_,
        );
    lean_dec(v_a_5334_);
    lean_dec_ref(v_a_5333_);
    lean_dec(v_a_5332_);
    lean_dec_ref(v_a_5331_);
    return v_res_5336_;
}
pub unsafe fn l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(
    mut v_ctorTerm_5337_: *mut LeanObject,
    mut v_e_5338_: *mut LeanObject,
    mut v_a_5339_: *mut LeanObject,
    mut v_a_5340_: *mut LeanObject,
    mut v_a_5341_: *mut LeanObject,
    mut v_a_5342_: *mut LeanObject,
    mut v_a_5343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5344_: *mut LeanObject = core::ptr::null_mut();
    v_res_5344_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_5337_, v_e_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_);
    lean_dec(v_a_5342_);
    lean_dec_ref(v_a_5341_);
    lean_dec(v_a_5340_);
    lean_dec_ref(v_a_5339_);
    return v_res_5344_;
}
pub unsafe fn l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(
    mut v_ctorTerm_5345_: *mut LeanObject,
    mut v_e_5346_: *mut LeanObject,
    mut v_a_5347_: *mut LeanObject,
    mut v_a_5348_: *mut LeanObject,
    mut v_a_5349_: *mut LeanObject,
    mut v_a_5350_: *mut LeanObject,
    mut v_a_5351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5352_: *mut LeanObject = core::ptr::null_mut();
    v_res_5352_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_5345_, v_e_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_);
    lean_dec(v_a_5350_);
    lean_dec_ref(v_a_5349_);
    lean_dec(v_a_5348_);
    lean_dec_ref(v_a_5347_);
    return v_res_5352_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    v___x_5354_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0;
    v___x_5355_ = l_Lean_stringToMessageData(v___x_5354_);
    return v___x_5355_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(
    mut v_constName_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5375_: u8 = 0;
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5362_ = lean_st_ref_get(v___y_5360_);
                v_env_5363_ = lean_ctor_get(v___x_5362_, 0);
                lean_inc_ref(v_env_5363_);
                lean_dec(v___x_5362_);
                lean_inc(v_constName_5356_);
                v___x_5364_ = l_Lean_isInductiveCore_x3f(v_env_5363_, v_constName_5356_);
                if lean_obj_tag(v___x_5364_) == 0 {
                    v___x_5365_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
                    v___x_5366_ = 0;
                    v___x_5367_ = l_Lean_MessageData_ofConstName(v_constName_5356_, v___x_5366_);
                    v___x_5368_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5368_, 0, v___x_5365_);
                    lean_ctor_set(v___x_5368_, 1, v___x_5367_);
                    v___x_5369_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
                    v___x_5370_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5370_, 0, v___x_5368_);
                    lean_ctor_set(v___x_5370_, 1, v___x_5369_);
                    v___x_5371_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_5370_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
                    return v___x_5371_;
                } else {
                    lean_dec(v_constName_5356_);
                    v_val_5372_ = lean_ctor_get(v___x_5364_, 0);
                    v_isSharedCheck_5379_ = (!lean_is_exclusive(v___x_5364_)) as u8;
                    if v_isSharedCheck_5379_ == 0 {
                        v___x_5374_ = v___x_5364_;
                        v_isShared_5375_ = v_isSharedCheck_5379_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5372_);
                        lean_dec(v___x_5364_);
                        v___x_5374_ = lean_box(0);
                        v_isShared_5375_ = v_isSharedCheck_5379_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5375_ == 0 {
                    lean_ctor_set_tag(v___x_5374_, 0);
                    v___x_5377_ = v___x_5374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_val_5372_);
                    v___x_5377_ = v_reuseFailAlloc_5378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(
    mut v_constName_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5386_: *mut LeanObject = core::ptr::null_mut();
    v_res_5386_ =
        l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(
            v_constName_5380_,
            v___y_5381_,
            v___y_5382_,
            v___y_5383_,
            v___y_5384_,
        );
    lean_dec(v___y_5384_);
    lean_dec_ref(v___y_5383_);
    lean_dec(v___y_5382_);
    lean_dec_ref(v___y_5381_);
    return v_res_5386_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(
    mut v_msg_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
    mut v___y_5392_: *mut LeanObject,
    mut v___y_5393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5400_: u8 = 0;
    let mut v_toFunctor_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5407_: u8 = 0;
    let mut v___f_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v_toFunctor_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5431_: u8 = 0;
    let mut v___f_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973__overap_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5450_: u8 = 0;
    let mut v_unused_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5452_: u8 = 0;
    let mut v_unused_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut v_unused_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_unused_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5395_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
                v___x_5396_ = l_StateRefT_x27_instMonad___redArg(v___x_5395_);
                v_toApplicative_5397_ = lean_ctor_get(v___x_5396_, 0);
                v_isSharedCheck_5458_ = (!lean_is_exclusive(v___x_5396_)) as u8;
                if v_isSharedCheck_5458_ == 0 {
                    v_unused_5459_ = lean_ctor_get(v___x_5396_, 1);
                    lean_dec(v_unused_5459_);
                    v___x_5399_ = v___x_5396_;
                    v_isShared_5400_ = v_isSharedCheck_5458_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5397_);
                    lean_dec(v___x_5396_);
                    v___x_5399_ = lean_box(0);
                    v_isShared_5400_ = v_isSharedCheck_5458_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5401_ = lean_ctor_get(v_toApplicative_5397_, 0);
                v_toSeq_5402_ = lean_ctor_get(v_toApplicative_5397_, 2);
                v_toSeqLeft_5403_ = lean_ctor_get(v_toApplicative_5397_, 3);
                v_toSeqRight_5404_ = lean_ctor_get(v_toApplicative_5397_, 4);
                v_isSharedCheck_5456_ = (!lean_is_exclusive(v_toApplicative_5397_)) as u8;
                if v_isSharedCheck_5456_ == 0 {
                    v_unused_5457_ = lean_ctor_get(v_toApplicative_5397_, 1);
                    lean_dec(v_unused_5457_);
                    v___x_5406_ = v_toApplicative_5397_;
                    v_isShared_5407_ = v_isSharedCheck_5456_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5404_);
                    lean_inc(v_toSeqLeft_5403_);
                    lean_inc(v_toSeq_5402_);
                    lean_inc(v_toFunctor_5401_);
                    lean_dec(v_toApplicative_5397_);
                    v___x_5406_ = lean_box(0);
                    v_isShared_5407_ = v_isSharedCheck_5456_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5408_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1;
                v___f_5409_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_5401_);
                v___f_5410_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5410_, 0, v_toFunctor_5401_);
                v___f_5411_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5411_, 0, v_toFunctor_5401_);
                v___x_5412_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5412_, 0, v___f_5410_);
                lean_ctor_set(v___x_5412_, 1, v___f_5411_);
                v___f_5413_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5413_, 0, v_toSeqRight_5404_);
                v___f_5414_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5414_, 0, v_toSeqLeft_5403_);
                v___f_5415_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5415_, 0, v_toSeq_5402_);
                if v_isShared_5407_ == 0 {
                    lean_ctor_set(v___x_5406_, 4, v___f_5413_);
                    lean_ctor_set(v___x_5406_, 3, v___f_5414_);
                    lean_ctor_set(v___x_5406_, 2, v___f_5415_);
                    lean_ctor_set(v___x_5406_, 1, v___f_5408_);
                    lean_ctor_set(v___x_5406_, 0, v___x_5412_);
                    v___x_5417_ = v___x_5406_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 0, v___x_5412_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___f_5408_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 2, v___f_5415_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 3, v___f_5414_);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 4, v___f_5413_);
                    v___x_5417_ = v_reuseFailAlloc_5455_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5400_ == 0 {
                    lean_ctor_set(v___x_5399_, 1, v___f_5409_);
                    lean_ctor_set(v___x_5399_, 0, v___x_5417_);
                    v___x_5419_ = v___x_5399_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5417_);
                    lean_ctor_set(v_reuseFailAlloc_5454_, 1, v___f_5409_);
                    v___x_5419_ = v_reuseFailAlloc_5454_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5420_ = l_StateRefT_x27_instMonad___redArg(v___x_5419_);
                v_toApplicative_5421_ = lean_ctor_get(v___x_5420_, 0);
                v_isSharedCheck_5452_ = (!lean_is_exclusive(v___x_5420_)) as u8;
                if v_isSharedCheck_5452_ == 0 {
                    v_unused_5453_ = lean_ctor_get(v___x_5420_, 1);
                    lean_dec(v_unused_5453_);
                    v___x_5423_ = v___x_5420_;
                    v_isShared_5424_ = v_isSharedCheck_5452_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5421_);
                    lean_dec(v___x_5420_);
                    v___x_5423_ = lean_box(0);
                    v_isShared_5424_ = v_isSharedCheck_5452_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5425_ = lean_ctor_get(v_toApplicative_5421_, 0);
                v_toSeq_5426_ = lean_ctor_get(v_toApplicative_5421_, 2);
                v_toSeqLeft_5427_ = lean_ctor_get(v_toApplicative_5421_, 3);
                v_toSeqRight_5428_ = lean_ctor_get(v_toApplicative_5421_, 4);
                v_isSharedCheck_5450_ = (!lean_is_exclusive(v_toApplicative_5421_)) as u8;
                if v_isSharedCheck_5450_ == 0 {
                    v_unused_5451_ = lean_ctor_get(v_toApplicative_5421_, 1);
                    lean_dec(v_unused_5451_);
                    v___x_5430_ = v_toApplicative_5421_;
                    v_isShared_5431_ = v_isSharedCheck_5450_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5428_);
                    lean_inc(v_toSeqLeft_5427_);
                    lean_inc(v_toSeq_5426_);
                    lean_inc(v_toFunctor_5425_);
                    lean_dec(v_toApplicative_5421_);
                    v___x_5430_ = lean_box(0);
                    v_isShared_5431_ = v_isSharedCheck_5450_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5432_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0;
                v___f_5433_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1;
                lean_inc_ref(v_toFunctor_5425_);
                v___f_5434_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5434_, 0, v_toFunctor_5425_);
                v___f_5435_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5435_, 0, v_toFunctor_5425_);
                v___x_5436_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5436_, 0, v___f_5434_);
                lean_ctor_set(v___x_5436_, 1, v___f_5435_);
                v___f_5437_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5437_, 0, v_toSeqRight_5428_);
                v___f_5438_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5438_, 0, v_toSeqLeft_5427_);
                v___f_5439_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5439_, 0, v_toSeq_5426_);
                if v_isShared_5431_ == 0 {
                    lean_ctor_set(v___x_5430_, 4, v___f_5437_);
                    lean_ctor_set(v___x_5430_, 3, v___f_5438_);
                    lean_ctor_set(v___x_5430_, 2, v___f_5439_);
                    lean_ctor_set(v___x_5430_, 1, v___f_5432_);
                    lean_ctor_set(v___x_5430_, 0, v___x_5436_);
                    v___x_5441_ = v___x_5430_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5436_);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___f_5432_);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 2, v___f_5439_);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 3, v___f_5438_);
                    lean_ctor_set(v_reuseFailAlloc_5449_, 4, v___f_5437_);
                    v___x_5441_ = v_reuseFailAlloc_5449_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5424_ == 0 {
                    lean_ctor_set(v___x_5423_, 1, v___f_5433_);
                    lean_ctor_set(v___x_5423_, 0, v___x_5441_);
                    v___x_5443_ = v___x_5423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5441_);
                    lean_ctor_set(v_reuseFailAlloc_5448_, 1, v___f_5433_);
                    v___x_5443_ = v_reuseFailAlloc_5448_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5444_ = lean_box(0);
                v___x_5445_ = l_instInhabitedOfMonad___redArg(v___x_5443_, v___x_5444_);
                v___x_3973__overap_5446_ = lean_panic_fn_borrowed(v___x_5445_, v_msg_5389_);
                lean_dec(v___x_5445_);
                lean_inc(v___y_5393_);
                lean_inc_ref(v___y_5392_);
                lean_inc(v___y_5391_);
                lean_inc_ref(v___y_5390_);
                v___x_5447_ = lean_apply_5(
                    v___x_3973__overap_5446_,
                    v___y_5390_,
                    v___y_5391_,
                    v___y_5392_,
                    v___y_5393_,
                    lean_box(0),
                );
                return v___x_5447_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(
    mut v_msg_5460_: *mut LeanObject,
    mut v___y_5461_: *mut LeanObject,
    mut v___y_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5466_: *mut LeanObject = core::ptr::null_mut();
    v_res_5466_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
    lean_dec(v___y_5464_);
    lean_dec_ref(v___y_5463_);
    lean_dec(v___y_5462_);
    lean_dec_ref(v___y_5461_);
    return v_res_5466_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(
    mut v_constName_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
    mut v___y_5469_: *mut LeanObject,
    mut v___y_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: u8 = 0;
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5486_: u8 = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5491_: u8 = 0;
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5495_: u8 = 0;
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5501_: u8 = 0;
    let mut v_val_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v_a_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5481_ = lean_st_ref_get(v___y_5471_);
                v_env_5482_ = lean_ctor_get(v___x_5481_, 0);
                lean_inc_ref(v_env_5482_);
                lean_dec(v___x_5481_);
                v___x_5483_ = 0;
                lean_inc(v_constName_5467_);
                v___x_5484_ =
                    l_Lean_Environment_findAsync_x3f(v_env_5482_, v_constName_5467_, v___x_5483_);
                if lean_obj_tag(v___x_5484_) == 1 {
                    v_val_5485_ = lean_ctor_get(v___x_5484_, 0);
                    lean_inc(v_val_5485_);
                    lean_dec_ref_known(v___x_5484_, 1);
                    v_kind_5486_ = lean_ctor_get_uint8(
                        v_val_5485_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_5486_ == 6 {
                        v___x_5487_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_5485_);
                        if lean_obj_tag(v___x_5487_) == 6 {
                            lean_dec(v_constName_5467_);
                            v_val_5488_ = lean_ctor_get(v___x_5487_, 0);
                            v_isSharedCheck_5495_ = (!lean_is_exclusive(v___x_5487_)) as u8;
                            if v_isSharedCheck_5495_ == 0 {
                                v___x_5490_ = v___x_5487_;
                                v_isShared_5491_ = v_isSharedCheck_5495_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_5488_);
                                lean_dec(v___x_5487_);
                                v___x_5490_ = lean_box(0);
                                v_isShared_5491_ = v_isSharedCheck_5495_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_5487_);
                            v___x_5496_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
                            v___x_5497_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_5496_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
                            if lean_obj_tag(v___x_5497_) == 0 {
                                v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
                                v_isSharedCheck_5506_ = (!lean_is_exclusive(v___x_5497_)) as u8;
                                if v_isSharedCheck_5506_ == 0 {
                                    v___x_5500_ = v___x_5497_;
                                    v_isShared_5501_ = v_isSharedCheck_5506_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_5498_);
                                    lean_dec(v___x_5497_);
                                    v___x_5500_ = lean_box(0);
                                    v_isShared_5501_ = v_isSharedCheck_5506_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_5467_);
                                v_a_5507_ = lean_ctor_get(v___x_5497_, 0);
                                v_isSharedCheck_5514_ = (!lean_is_exclusive(v___x_5497_)) as u8;
                                if v_isSharedCheck_5514_ == 0 {
                                    v___x_5509_ = v___x_5497_;
                                    v_isShared_5510_ = v_isSharedCheck_5514_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5507_);
                                    lean_dec(v___x_5497_);
                                    v___x_5509_ = lean_box(0);
                                    v_isShared_5510_ = v_isSharedCheck_5514_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_5485_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5484_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5474_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
                v___x_5475_ = 0;
                v___x_5476_ = l_Lean_MessageData_ofConstName(v_constName_5467_, v___x_5475_);
                v___x_5477_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5477_, 0, v___x_5474_);
                lean_ctor_set(v___x_5477_, 1, v___x_5476_);
                v___x_5478_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
                v___x_5479_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5479_, 0, v___x_5477_);
                lean_ctor_set(v___x_5479_, 1, v___x_5478_);
                v___x_5480_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_5479_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
                return v___x_5480_;
            }
            2 => {
                if v_isShared_5491_ == 0 {
                    lean_ctor_set_tag(v___x_5490_, 0);
                    v___x_5493_ = v___x_5490_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_val_5488_);
                    v___x_5493_ = v_reuseFailAlloc_5494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5493_;
            }
            4 => {
                if lean_obj_tag(v_a_5498_) == 0 {
                    lean_del_object(v___x_5500_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_5467_);
                    v_val_5502_ = lean_ctor_get(v_a_5498_, 0);
                    lean_inc(v_val_5502_);
                    lean_dec_ref_known(v_a_5498_, 1);
                    if v_isShared_5501_ == 0 {
                        lean_ctor_set(v___x_5500_, 0, v_val_5502_);
                        v___x_5504_ = v___x_5500_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_val_5502_);
                        v___x_5504_ = v_reuseFailAlloc_5505_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5504_;
            }
            6 => {
                if v_isShared_5510_ == 0 {
                    v___x_5512_ = v___x_5509_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
                    v___x_5512_ = v_reuseFailAlloc_5513_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(
    mut v_constName_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5521_: *mut LeanObject = core::ptr::null_mut();
    v_res_5521_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(
            v_constName_5515_,
            v___y_5516_,
            v___y_5517_,
            v___y_5518_,
            v___y_5519_,
        );
    lean_dec(v___y_5519_);
    lean_dec_ref(v___y_5518_);
    lean_dec(v___y_5517_);
    lean_dec_ref(v___y_5516_);
    return v_res_5521_;
}
pub unsafe fn _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1() -> *mut LeanObject
{
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    v___x_5523_ = l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0;
    v___x_5524_ = l_Lean_stringToMessageData(v___x_5523_);
    return v___x_5524_;
}
pub unsafe fn _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3() -> *mut LeanObject
{
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    v___x_5526_ = l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2;
    v___x_5527_ = l_Lean_stringToMessageData(v___x_5526_);
    return v___x_5527_;
}
pub unsafe fn _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4() -> *mut LeanObject
{
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5529_: *mut LeanObject = core::ptr::null_mut();
    v___x_5528_ = lean_box(0);
    v_dummy_5529_ = l_Lean_Expr_sort___override(v___x_5528_);
    return v_dummy_5529_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_getComputedFieldValue(
    mut v_computedField_5530_: *mut LeanObject,
    mut v_ctorTerm_5531_: *mut LeanObject,
    mut v_a_5532_: *mut LeanObject,
    mut v_a_5533_: *mut LeanObject,
    mut v_a_5534_: *mut LeanObject,
    mut v_a_5535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: u8 = 0;
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_induct_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: u8 = 0;
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_a_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5537_ = l_Lean_Expr_getAppFn(v_ctorTerm_5531_);
                v_ctorName_5538_ = l_Lean_Expr_constName_x21(v___x_5537_);
                lean_dec_ref(v___x_5537_);
                lean_inc(v_ctorName_5538_);
                v___x_5556_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_5538_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
                if lean_obj_tag(v___x_5556_) == 0 {
                    v_a_5557_ = lean_ctor_get(v___x_5556_, 0);
                    lean_inc(v_a_5557_);
                    lean_dec_ref_known(v___x_5556_, 1);
                    v_induct_5558_ = lean_ctor_get(v_a_5557_, 1);
                    lean_inc(v_induct_5558_);
                    lean_dec(v_a_5557_);
                    v___x_5559_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_5558_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
                    if lean_obj_tag(v___x_5559_) == 0 {
                        v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
                        lean_inc(v_a_5560_);
                        lean_dec_ref_known(v___x_5559_, 1);
                        v_numParams_5561_ = lean_ctor_get(v_a_5560_, 1);
                        lean_inc(v_numParams_5561_);
                        v_numIndices_5562_ = lean_ctor_get(v_a_5560_, 2);
                        lean_inc(v_numIndices_5562_);
                        lean_dec(v_a_5560_);
                        v___x_5563_ = lean_nat_add(v_numParams_5561_, v_numIndices_5562_);
                        lean_dec(v_numIndices_5562_);
                        lean_dec(v_numParams_5561_);
                        v___x_5564_ = lean_box(0);
                        v___x_5565_ = lean_mk_array(v___x_5563_, v___x_5564_);
                        lean_inc_ref(v_ctorTerm_5531_);
                        v___x_5566_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5566_, 0, v_ctorTerm_5531_);
                        v___x_5567_ = lean_unsigned_to_nat(1);
                        v___x_5568_ = lean_mk_empty_array_with_capacity(v___x_5567_);
                        v___x_5569_ = lean_array_push(v___x_5568_, v___x_5566_);
                        v___x_5570_ = l_Array_append___redArg(v___x_5565_, v___x_5569_);
                        lean_dec_ref(v___x_5569_);
                        lean_inc(v_computedField_5530_);
                        v___x_5571_ = l_Lean_Meta_mkAppOptM(
                            v_computedField_5530_,
                            v___x_5570_,
                            v_a_5532_,
                            v_a_5533_,
                            v_a_5534_,
                            v_a_5535_,
                        );
                        if lean_obj_tag(v___x_5571_) == 0 {
                            v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
                            lean_inc(v_a_5572_);
                            lean_dec_ref_known(v___x_5571_, 1);
                            v___x_5573_ = lean_st_ref_get(v_a_5535_);
                            v_env_5574_ = lean_ctor_get(v___x_5573_, 0);
                            lean_inc_ref(v_env_5574_);
                            lean_dec(v___x_5573_);
                            v___x_5575_ = l_Lean_Elab_WF_eqnInfoExt;
                            v_toEnvExtension_5576_ = lean_ctor_get(v___x_5575_, 0);
                            v_asyncMode_5577_ = lean_ctor_get(v_toEnvExtension_5576_, 2);
                            v___x_5578_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
                            v___x_5579_ = 0;
                            lean_inc(v_computedField_5530_);
                            v___x_5580_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                                v___x_5578_,
                                v___x_5575_,
                                v_env_5574_,
                                v_computedField_5530_,
                                v_asyncMode_5577_,
                                v___x_5579_,
                            );
                            if lean_obj_tag(v___x_5580_) == 1 {
                                v_val_5581_ = lean_ctor_get(v___x_5580_, 0);
                                lean_inc(v_val_5581_);
                                lean_dec_ref_known(v___x_5580_, 1);
                                v_levelParams_5582_ = lean_ctor_get(v_val_5581_, 1);
                                lean_inc(v_levelParams_5582_);
                                v_value_5583_ = lean_ctor_get(v_val_5581_, 3);
                                lean_inc_ref(v_value_5583_);
                                lean_dec(v_val_5581_);
                                v___x_5584_ = l_Lean_Expr_getAppFn(v_a_5572_);
                                v___x_5585_ = l_Lean_Expr_constLevels_x21(v___x_5584_);
                                lean_dec_ref(v___x_5584_);
                                v___x_5586_ = l_Lean_Expr_instantiateLevelParams(
                                    v_value_5583_,
                                    v_levelParams_5582_,
                                    v___x_5585_,
                                );
                                lean_dec_ref(v_value_5583_);
                                v_dummy_5587_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once), _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
                                v_nargs_5588_ = l_Lean_Expr_getAppNumArgs(v_a_5572_);
                                lean_inc(v_nargs_5588_);
                                v___x_5589_ = lean_mk_array(v_nargs_5588_, v_dummy_5587_);
                                v___x_5590_ = lean_nat_sub(v_nargs_5588_, v___x_5567_);
                                lean_dec(v_nargs_5588_);
                                v___x_5591_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                    v_a_5572_,
                                    v___x_5589_,
                                    v___x_5590_,
                                );
                                v___x_5592_ = l_Lean_mkAppN(v___x_5586_, v___x_5591_);
                                lean_dec_ref(v___x_5591_);
                                v_val_5540_ = v___x_5592_;
                                v___y_5541_ = v_a_5532_;
                                v___y_5542_ = v_a_5533_;
                                v___y_5543_ = v_a_5534_;
                                v___y_5544_ = v_a_5535_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_5580_);
                                v___x_5593_ = l_Lean_Meta_unfoldDefinition(
                                    v_a_5572_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_,
                                );
                                if lean_obj_tag(v___x_5593_) == 0 {
                                    v_a_5594_ = lean_ctor_get(v___x_5593_, 0);
                                    lean_inc(v_a_5594_);
                                    lean_dec_ref_known(v___x_5593_, 1);
                                    v_val_5540_ = v_a_5594_;
                                    v___y_5541_ = v_a_5532_;
                                    v___y_5542_ = v_a_5533_;
                                    v___y_5543_ = v_a_5534_;
                                    v___y_5544_ = v_a_5535_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_ctorName_5538_);
                                    lean_dec_ref(v_ctorTerm_5531_);
                                    lean_dec(v_computedField_5530_);
                                    return v___x_5593_;
                                }
                            }
                        } else {
                            lean_dec(v_ctorName_5538_);
                            lean_dec_ref(v_ctorTerm_5531_);
                            lean_dec(v_computedField_5530_);
                            return v___x_5571_;
                        }
                    } else {
                        lean_dec(v_ctorName_5538_);
                        lean_dec_ref(v_ctorTerm_5531_);
                        lean_dec(v_computedField_5530_);
                        v_a_5595_ = lean_ctor_get(v___x_5559_, 0);
                        v_isSharedCheck_5602_ = (!lean_is_exclusive(v___x_5559_)) as u8;
                        if v_isSharedCheck_5602_ == 0 {
                            v___x_5597_ = v___x_5559_;
                            v_isShared_5598_ = v_isSharedCheck_5602_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5595_);
                            lean_dec(v___x_5559_);
                            v___x_5597_ = lean_box(0);
                            v_isShared_5598_ = v_isSharedCheck_5602_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_ctorName_5538_);
                    lean_dec_ref(v_ctorTerm_5531_);
                    lean_dec(v_computedField_5530_);
                    v_a_5603_ = lean_ctor_get(v___x_5556_, 0);
                    v_isSharedCheck_5610_ = (!lean_is_exclusive(v___x_5556_)) as u8;
                    if v_isSharedCheck_5610_ == 0 {
                        v___x_5605_ = v___x_5556_;
                        v_isShared_5606_ = v_isSharedCheck_5610_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5603_);
                        lean_dec(v___x_5556_);
                        v___x_5605_ = lean_box(0);
                        v_isShared_5606_ = v_isSharedCheck_5610_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_ctorTerm_5531_);
                v___x_5545_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_5531_, v_val_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_);
                if lean_obj_tag(v___x_5545_) == 0 {
                    v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
                    lean_inc(v_a_5546_);
                    v___x_5547_ = l_Lean_Expr_occurs(v_ctorTerm_5531_, v_a_5546_);
                    lean_dec(v_a_5546_);
                    if v___x_5547_ == 0 {
                        lean_dec(v_ctorName_5538_);
                        lean_dec(v_computedField_5530_);
                        return v___x_5545_;
                    } else {
                        lean_dec_ref_known(v___x_5545_, 1);
                        v___x_5548_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once
                            ),
                            _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1,
                        );
                        v___x_5549_ = l_Lean_MessageData_ofName(v_computedField_5530_);
                        v___x_5550_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5550_, 0, v___x_5548_);
                        lean_ctor_set(v___x_5550_, 1, v___x_5549_);
                        v___x_5551_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once
                            ),
                            _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3,
                        );
                        v___x_5552_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5552_, 0, v___x_5550_);
                        lean_ctor_set(v___x_5552_, 1, v___x_5551_);
                        v___x_5553_ = l_Lean_MessageData_ofName(v_ctorName_5538_);
                        v___x_5554_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5554_, 0, v___x_5552_);
                        lean_ctor_set(v___x_5554_, 1, v___x_5553_);
                        v___x_5555_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_5554_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_);
                        return v___x_5555_;
                    }
                } else {
                    lean_dec(v_ctorName_5538_);
                    lean_dec_ref(v_ctorTerm_5531_);
                    lean_dec(v_computedField_5530_);
                    return v___x_5545_;
                }
            }
            2 => {
                if v_isShared_5598_ == 0 {
                    v___x_5600_ = v___x_5597_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
                    v___x_5600_ = v_reuseFailAlloc_5601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5600_;
            }
            4 => {
                if v_isShared_5606_ == 0 {
                    v___x_5608_ = v___x_5605_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(
    mut v_computedField_5611_: *mut LeanObject,
    mut v_ctorTerm_5612_: *mut LeanObject,
    mut v_a_5613_: *mut LeanObject,
    mut v_a_5614_: *mut LeanObject,
    mut v_a_5615_: *mut LeanObject,
    mut v_a_5616_: *mut LeanObject,
    mut v_a_5617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5618_: *mut LeanObject = core::ptr::null_mut();
    v_res_5618_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(
        v_computedField_5611_,
        v_ctorTerm_5612_,
        v_a_5613_,
        v_a_5614_,
        v_a_5615_,
        v_a_5616_,
    );
    lean_dec(v_a_5616_);
    lean_dec_ref(v_a_5615_);
    lean_dec(v_a_5614_);
    lean_dec_ref(v_a_5613_);
    return v_res_5618_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(
    mut v_00_u03b1_5619_: *mut LeanObject,
    mut v_msg_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
    mut v___y_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    v___x_5626_ =
        l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(
            v_msg_5620_,
            v___y_5621_,
            v___y_5622_,
            v___y_5623_,
            v___y_5624_,
        );
    return v___x_5626_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(
    mut v_00_u03b1_5627_: *mut LeanObject,
    mut v_msg_5628_: *mut LeanObject,
    mut v___y_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
    mut v___y_5631_: *mut LeanObject,
    mut v___y_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5634_: *mut LeanObject = core::ptr::null_mut();
    v_res_5634_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(
        v_00_u03b1_5627_,
        v_msg_5628_,
        v___y_5629_,
        v___y_5630_,
        v___y_5631_,
        v___y_5632_,
    );
    lean_dec(v___y_5632_);
    lean_dec_ref(v___y_5631_);
    lean_dec(v___y_5630_);
    lean_dec_ref(v___y_5629_);
    return v_res_5634_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(
    mut v_mvarId_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    v___x_5641_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_5635_, v___y_5637_);
    return v___x_5641_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(
    mut v_mvarId_5642_: *mut LeanObject,
    mut v___y_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
    mut v___y_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5648_: *mut LeanObject = core::ptr::null_mut();
    v_res_5648_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_);
    lean_dec(v___y_5646_);
    lean_dec_ref(v___y_5645_);
    lean_dec(v___y_5644_);
    lean_dec_ref(v___y_5643_);
    lean_dec(v_mvarId_5642_);
    return v_res_5648_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(
    mut v_00_u03b2_5649_: *mut LeanObject,
    mut v_k_5650_: *mut LeanObject,
    mut v_t_5651_: *mut LeanObject,
) -> u8 {
    let mut v___x_5652_: u8 = 0;
    v___x_5652_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_5650_, v_t_5651_);
    return v___x_5652_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_5653_: *mut LeanObject,
    mut v_k_5654_: *mut LeanObject,
    mut v_t_5655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5656_: u8 = 0;
    let mut v_r_5657_: *mut LeanObject = core::ptr::null_mut();
    v_res_5656_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_5653_, v_k_5654_, v_t_5655_);
    lean_dec(v_t_5655_);
    lean_dec(v_k_5654_);
    v_r_5657_ = lean_box((v_res_5656_) as usize);
    return v_r_5657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(
    mut v_a_5658_: *mut LeanObject,
    mut v_as_5659_: *mut LeanObject,
    mut v_i_5660_: usize,
    mut v_stop_5661_: usize,
) -> u8 {
    let mut v___x_5662_: u8 = 0;
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: u8 = 0;
    let mut v___x_5666_: usize = 0;
    let mut v___x_5667_: usize = 0;
    let mut v___x_5669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5662_ = lean_usize_dec_eq(v_i_5660_, v_stop_5661_);
                if v___x_5662_ == 0 {
                    v___x_5663_ = lean_array_uget_borrowed(v_as_5659_, v_i_5660_);
                    v___x_5664_ = l_Lean_Expr_fvarId_x21(v___x_5663_);
                    v___x_5665_ = l_Lean_Expr_containsFVar(v_a_5658_, v___x_5664_);
                    lean_dec(v___x_5664_);
                    if v___x_5665_ == 0 {
                        v___x_5666_ = 1usize;
                        v___x_5667_ = lean_usize_add(v_i_5660_, v___x_5666_);
                        v_i_5660_ = v___x_5667_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5665_;
                    }
                } else {
                    v___x_5669_ = 0;
                    return v___x_5669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(
    mut v_a_5670_: *mut LeanObject,
    mut v_as_5671_: *mut LeanObject,
    mut v_i_5672_: *mut LeanObject,
    mut v_stop_5673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5674_: usize = 0;
    let mut v_stop_boxed_5675_: usize = 0;
    let mut v_res_5676_: u8 = 0;
    let mut v_r_5677_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5674_ = lean_unbox_usize(v_i_5672_);
    lean_dec(v_i_5672_);
    v_stop_boxed_5675_ = lean_unbox_usize(v_stop_5673_);
    lean_dec(v_stop_5673_);
    v_res_5676_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_5670_, v_as_5671_, v_i_boxed_5674_, v_stop_boxed_5675_);
    lean_dec_ref(v_as_5671_);
    lean_dec_ref(v_a_5670_);
    v_r_5677_ = lean_box((v_res_5676_) as usize);
    return v_r_5677_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(
    mut v_msg_5678_: *mut LeanObject,
    mut v___y_5679_: *mut LeanObject,
    mut v___y_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5689_: u8 = 0;
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5684_ = lean_ctor_get(v___y_5681_, 5);
                v___x_5685_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
                v_a_5686_ = lean_ctor_get(v___x_5685_, 0);
                v_isSharedCheck_5694_ = (!lean_is_exclusive(v___x_5685_)) as u8;
                if v_isSharedCheck_5694_ == 0 {
                    v___x_5688_ = v___x_5685_;
                    v_isShared_5689_ = v_isSharedCheck_5694_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5686_);
                    lean_dec(v___x_5685_);
                    v___x_5688_ = lean_box(0);
                    v_isShared_5689_ = v_isSharedCheck_5694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5684_);
                v___x_5690_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5690_, 0, v_ref_5684_);
                lean_ctor_set(v___x_5690_, 1, v_a_5686_);
                if v_isShared_5689_ == 0 {
                    lean_ctor_set_tag(v___x_5688_, 1);
                    lean_ctor_set(v___x_5688_, 0, v___x_5690_);
                    v___x_5692_ = v___x_5688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5693_, 0, v___x_5690_);
                    v___x_5692_ = v_reuseFailAlloc_5693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(
    mut v_msg_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5701_: *mut LeanObject = core::ptr::null_mut();
    v_res_5701_ =
        l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(
            v_msg_5695_,
            v___y_5696_,
            v___y_5697_,
            v___y_5698_,
            v___y_5699_,
        );
    lean_dec(v___y_5699_);
    lean_dec_ref(v___y_5698_);
    lean_dec(v___y_5697_);
    lean_dec_ref(v___y_5696_);
    return v_res_5701_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    v___x_5703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0;
    v___x_5704_ = l_Lean_stringToMessageData(v___x_5703_);
    return v___x_5704_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    v___x_5706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2;
    v___x_5707_ = l_Lean_stringToMessageData(v___x_5706_);
    return v___x_5707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(
    mut v_indices_5708_: *mut LeanObject,
    mut v_val_5709_: *mut LeanObject,
    mut v_as_5710_: *mut LeanObject,
    mut v_sz_5711_: usize,
    mut v_i_5712_: usize,
    mut v_b_5713_: *mut LeanObject,
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
    mut v___y_5717_: *mut LeanObject,
    mut v___y_5718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: usize = 0;
    let mut v___x_5723_: usize = 0;
    let mut v___x_5725_: u8 = 0;
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: usize = 0;
    let mut v___x_5741_: usize = 0;
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: u8 = 0;
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5764_: u8 = 0;
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5725_ = lean_usize_dec_lt(v_i_5712_, v_sz_5711_);
                if v___x_5725_ == 0 {
                    v___x_5726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5726_, 0, v_b_5713_);
                    return v___x_5726_;
                } else {
                    v_a_5727_ = lean_array_uget_borrowed(v_as_5710_, v_i_5712_);
                    lean_inc(v___y_5718_);
                    lean_inc_ref(v___y_5717_);
                    lean_inc(v___y_5716_);
                    lean_inc_ref(v___y_5715_);
                    lean_inc(v_a_5727_);
                    v___x_5728_ = lean_infer_type(
                        v_a_5727_,
                        v___y_5715_,
                        v___y_5716_,
                        v___y_5717_,
                        v___y_5718_,
                    );
                    if lean_obj_tag(v___x_5728_) == 0 {
                        v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
                        lean_inc(v_a_5729_);
                        lean_dec_ref_known(v___x_5728_, 1);
                        v___x_5730_ = lean_box(0);
                        v___x_5751_ = l_Lean_Expr_fvarId_x21(v_val_5709_);
                        v___x_5752_ = l_Lean_Expr_containsFVar(v_a_5729_, v___x_5751_);
                        lean_dec(v___x_5751_);
                        if v___x_5752_ == 0 {
                            v___y_5732_ = v___y_5714_;
                            v___y_5733_ = v___y_5715_;
                            v___y_5734_ = v___y_5716_;
                            v___y_5735_ = v___y_5717_;
                            v___y_5736_ = v___y_5718_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5753_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once), _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
                            lean_inc(v_a_5727_);
                            v___x_5754_ = l_Lean_MessageData_ofExpr(v_a_5727_);
                            v___x_5755_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5755_, 0, v___x_5753_);
                            lean_ctor_set(v___x_5755_, 1, v___x_5754_);
                            v___x_5756_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
                            v___x_5757_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5757_, 0, v___x_5755_);
                            lean_ctor_set(v___x_5757_, 1, v___x_5756_);
                            lean_inc(v_a_5729_);
                            v___x_5758_ = l_Lean_indentExpr(v_a_5729_);
                            v___x_5759_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5759_, 0, v___x_5757_);
                            lean_ctor_set(v___x_5759_, 1, v___x_5758_);
                            v___x_5760_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_5759_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_);
                            if lean_obj_tag(v___x_5760_) == 0 {
                                lean_dec_ref_known(v___x_5760_, 1);
                                v___y_5732_ = v___y_5714_;
                                v___y_5733_ = v___y_5715_;
                                v___y_5734_ = v___y_5716_;
                                v___y_5735_ = v___y_5717_;
                                v___y_5736_ = v___y_5718_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_5729_);
                                return v___x_5760_;
                            }
                        }
                    } else {
                        v_a_5761_ = lean_ctor_get(v___x_5728_, 0);
                        v_isSharedCheck_5768_ = (!lean_is_exclusive(v___x_5728_)) as u8;
                        if v_isSharedCheck_5768_ == 0 {
                            v___x_5763_ = v___x_5728_;
                            v_isShared_5764_ = v_isSharedCheck_5768_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5761_);
                            lean_dec(v___x_5728_);
                            v___x_5763_ = lean_box(0);
                            v_isShared_5764_ = v_isSharedCheck_5768_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5722_ = 1usize;
                v___x_5723_ = lean_usize_add(v_i_5712_, v___x_5722_);
                v_i_5712_ = v___x_5723_;
                v_b_5713_ = v_a_5721_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5737_ = lean_unsigned_to_nat(0);
                v___x_5738_ = lean_array_get_size(v_indices_5708_);
                v___x_5739_ = lean_nat_dec_lt(v___x_5737_, v___x_5738_);
                if v___x_5739_ == 0 {
                    lean_dec(v_a_5729_);
                    v_a_5721_ = v___x_5730_;
                    state = 1;
                    continue;
                } else {
                    if v___x_5739_ == 0 {
                        lean_dec(v_a_5729_);
                        v_a_5721_ = v___x_5730_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5740_ = 0usize;
                        v___x_5741_ = lean_usize_of_nat(v___x_5738_);
                        v___x_5742_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_5729_, v_indices_5708_, v___x_5740_, v___x_5741_);
                        if v___x_5742_ == 0 {
                            lean_dec(v_a_5729_);
                            v_a_5721_ = v___x_5730_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once), _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
                            lean_inc(v_a_5727_);
                            v___x_5744_ = l_Lean_MessageData_ofExpr(v_a_5727_);
                            v___x_5745_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5745_, 0, v___x_5743_);
                            lean_ctor_set(v___x_5745_, 1, v___x_5744_);
                            v___x_5746_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
                            v___x_5747_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5747_, 0, v___x_5745_);
                            lean_ctor_set(v___x_5747_, 1, v___x_5746_);
                            v___x_5748_ = l_Lean_indentExpr(v_a_5729_);
                            v___x_5749_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_5749_, 0, v___x_5747_);
                            lean_ctor_set(v___x_5749_, 1, v___x_5748_);
                            v___x_5750_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_5749_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_);
                            if lean_obj_tag(v___x_5750_) == 0 {
                                lean_dec_ref_known(v___x_5750_, 1);
                                v_a_5721_ = v___x_5730_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_5750_;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_5764_ == 0 {
                    v___x_5766_ = v___x_5763_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
                    v___x_5766_ = v_reuseFailAlloc_5767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(
    mut v_indices_5769_: *mut LeanObject,
    mut v_val_5770_: *mut LeanObject,
    mut v_as_5771_: *mut LeanObject,
    mut v_sz_5772_: *mut LeanObject,
    mut v_i_5773_: *mut LeanObject,
    mut v_b_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5781_: usize = 0;
    let mut v_i_boxed_5782_: usize = 0;
    let mut v_res_5783_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5781_ = lean_unbox_usize(v_sz_5772_);
    lean_dec(v_sz_5772_);
    v_i_boxed_5782_ = lean_unbox_usize(v_i_5773_);
    lean_dec(v_i_5773_);
    v_res_5783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_5769_, v_val_5770_, v_as_5771_, v_sz_boxed_5781_, v_i_boxed_5782_, v_b_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_);
    lean_dec(v___y_5779_);
    lean_dec_ref(v___y_5778_);
    lean_dec(v___y_5777_);
    lean_dec_ref(v___y_5776_);
    lean_dec_ref(v___y_5775_);
    lean_dec_ref(v_as_5771_);
    lean_dec_ref(v_val_5770_);
    lean_dec_ref(v_indices_5769_);
    return v_res_5783_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_validateComputedFields(
    mut v_a_5784_: *mut LeanObject,
    mut v_a_5785_: *mut LeanObject,
    mut v_a_5786_: *mut LeanObject,
    mut v_a_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_compFieldVars_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5794_: usize = 0;
    let mut v___x_5795_: usize = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5799_: u8 = 0;
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5803_: u8 = 0;
    let mut v_unused_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_compFieldVars_5790_ = lean_ctor_get(v_a_5784_, 4);
                v_indices_5791_ = lean_ctor_get(v_a_5784_, 5);
                v_val_5792_ = lean_ctor_get(v_a_5784_, 6);
                v___x_5793_ = lean_box(0);
                v_sz_5794_ = lean_array_size(v_compFieldVars_5790_);
                v___x_5795_ = 0usize;
                v___x_5796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_5791_, v_val_5792_, v_compFieldVars_5790_, v_sz_5794_, v___x_5795_, v___x_5793_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_);
                if lean_obj_tag(v___x_5796_) == 0 {
                    v_isSharedCheck_5803_ = (!lean_is_exclusive(v___x_5796_)) as u8;
                    if v_isSharedCheck_5803_ == 0 {
                        v_unused_5804_ = lean_ctor_get(v___x_5796_, 0);
                        lean_dec(v_unused_5804_);
                        v___x_5798_ = v___x_5796_;
                        v_isShared_5799_ = v_isSharedCheck_5803_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5796_);
                        v___x_5798_ = lean_box(0);
                        v_isShared_5799_ = v_isSharedCheck_5803_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_5796_;
                }
            }
            1 => {
                if v_isShared_5799_ == 0 {
                    lean_ctor_set(v___x_5798_, 0, v___x_5793_);
                    v___x_5801_ = v___x_5798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5793_);
                    v___x_5801_ = v_reuseFailAlloc_5802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_validateComputedFields___boxed(
    mut v_a_5805_: *mut LeanObject,
    mut v_a_5806_: *mut LeanObject,
    mut v_a_5807_: *mut LeanObject,
    mut v_a_5808_: *mut LeanObject,
    mut v_a_5809_: *mut LeanObject,
    mut v_a_5810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5811_: *mut LeanObject = core::ptr::null_mut();
    v_res_5811_ = l_Lean_Elab_ComputedFields_validateComputedFields(
        v_a_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_,
    );
    lean_dec(v_a_5809_);
    lean_dec_ref(v_a_5808_);
    lean_dec(v_a_5807_);
    lean_dec_ref(v_a_5806_);
    lean_dec_ref(v_a_5805_);
    return v_res_5811_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(
    mut v_00_u03b1_5812_: *mut LeanObject,
    mut v_msg_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    v___x_5820_ =
        l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(
            v_msg_5813_,
            v___y_5815_,
            v___y_5816_,
            v___y_5817_,
            v___y_5818_,
        );
    return v___x_5820_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(
    mut v_00_u03b1_5821_: *mut LeanObject,
    mut v_msg_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
    mut v___y_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5829_: *mut LeanObject = core::ptr::null_mut();
    v_res_5829_ =
        l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(
            v_00_u03b1_5821_,
            v_msg_5822_,
            v___y_5823_,
            v___y_5824_,
            v___y_5825_,
            v___y_5826_,
            v___y_5827_,
        );
    lean_dec(v___y_5827_);
    lean_dec_ref(v___y_5826_);
    lean_dec(v___y_5825_);
    lean_dec_ref(v___y_5824_);
    lean_dec_ref(v___y_5823_);
    return v_res_5829_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(
    mut v_k_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
    mut v_b_5832_: *mut LeanObject,
    mut v_c_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5837_);
    lean_inc_ref(v___y_5836_);
    lean_inc(v___y_5835_);
    lean_inc_ref(v___y_5834_);
    lean_inc_ref(v___y_5831_);
    v___x_5839_ = lean_apply_8(
        v_k_5830_,
        v_b_5832_,
        v_c_5833_,
        v___y_5831_,
        v___y_5834_,
        v___y_5835_,
        v___y_5836_,
        v___y_5837_,
        lean_box(0),
    );
    return v___x_5839_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(
    mut v_k_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v_b_5842_: *mut LeanObject,
    mut v_c_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5849_: *mut LeanObject = core::ptr::null_mut();
    v_res_5849_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_5840_, v___y_5841_, v_b_5842_, v_c_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
    lean_dec(v___y_5847_);
    lean_dec_ref(v___y_5846_);
    lean_dec(v___y_5845_);
    lean_dec_ref(v___y_5844_);
    lean_dec_ref(v___y_5841_);
    return v_res_5849_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(
    mut v_type_5850_: *mut LeanObject,
    mut v_k_5851_: *mut LeanObject,
    mut v_cleanupAnnotations_5852_: u8,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
    mut v___y_5856_: *mut LeanObject,
    mut v___y_5857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: u8 = 0;
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_5853_);
                v___f_5859_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                lean_closure_set(v___f_5859_, 0, v_k_5851_);
                lean_closure_set(v___f_5859_, 1, v___y_5853_);
                v___x_5860_ = 0;
                v___x_5861_ = lean_box(0);
                v___x_5862_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_5860_,
                        v___x_5861_,
                        v_type_5850_,
                        v___f_5859_,
                        v_cleanupAnnotations_5852_,
                        v___x_5860_,
                        v___y_5854_,
                        v___y_5855_,
                        v___y_5856_,
                        v___y_5857_,
                    );
                if lean_obj_tag(v___x_5862_) == 0 {
                    return v___x_5862_;
                } else {
                    v_a_5863_ = lean_ctor_get(v___x_5862_, 0);
                    v_isSharedCheck_5870_ = (!lean_is_exclusive(v___x_5862_)) as u8;
                    if v_isSharedCheck_5870_ == 0 {
                        v___x_5865_ = v___x_5862_;
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5863_);
                        lean_dec(v___x_5862_);
                        v___x_5865_ = lean_box(0);
                        v_isShared_5866_ = v_isSharedCheck_5870_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5866_ == 0 {
                    v___x_5868_ = v___x_5865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
                    v___x_5868_ = v_reuseFailAlloc_5869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(
    mut v_type_5871_: *mut LeanObject,
    mut v_k_5872_: *mut LeanObject,
    mut v_cleanupAnnotations_5873_: *mut LeanObject,
    mut v___y_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
    mut v___y_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5880_: u8 = 0;
    let mut v_res_5881_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5880_ = (lean_unbox(v_cleanupAnnotations_5873_) as u8);
    v_res_5881_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(
            v_type_5871_,
            v_k_5872_,
            v_cleanupAnnotations_boxed_5880_,
            v___y_5874_,
            v___y_5875_,
            v___y_5876_,
            v___y_5877_,
            v___y_5878_,
        );
    lean_dec(v___y_5878_);
    lean_dec_ref(v___y_5877_);
    lean_dec(v___y_5876_);
    lean_dec_ref(v___y_5875_);
    lean_dec_ref(v___y_5874_);
    return v_res_5881_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(
    mut v_00_u03b1_5882_: *mut LeanObject,
    mut v_type_5883_: *mut LeanObject,
    mut v_k_5884_: *mut LeanObject,
    mut v_cleanupAnnotations_5885_: u8,
    mut v___y_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
    mut v___y_5889_: *mut LeanObject,
    mut v___y_5890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    v___x_5892_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(
            v_type_5883_,
            v_k_5884_,
            v_cleanupAnnotations_5885_,
            v___y_5886_,
            v___y_5887_,
            v___y_5888_,
            v___y_5889_,
            v___y_5890_,
        );
    return v___x_5892_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(
    mut v_00_u03b1_5893_: *mut LeanObject,
    mut v_type_5894_: *mut LeanObject,
    mut v_k_5895_: *mut LeanObject,
    mut v_cleanupAnnotations_5896_: *mut LeanObject,
    mut v___y_5897_: *mut LeanObject,
    mut v___y_5898_: *mut LeanObject,
    mut v___y_5899_: *mut LeanObject,
    mut v___y_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5903_: u8 = 0;
    let mut v_res_5904_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5903_ = (lean_unbox(v_cleanupAnnotations_5896_) as u8);
    v_res_5904_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(
        v_00_u03b1_5893_,
        v_type_5894_,
        v_k_5895_,
        v_cleanupAnnotations_boxed_5903_,
        v___y_5897_,
        v___y_5898_,
        v___y_5899_,
        v___y_5900_,
        v___y_5901_,
    );
    lean_dec(v___y_5901_);
    lean_dec_ref(v___y_5900_);
    lean_dec(v___y_5899_);
    lean_dec_ref(v___y_5898_);
    lean_dec_ref(v___y_5897_);
    return v_res_5904_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(
    mut v_head_5910_: *mut LeanObject,
    mut v_name_5911_: *mut LeanObject,
    mut v_lparams_5912_: *mut LeanObject,
    mut v_params_5913_: *mut LeanObject,
    mut v_compFieldVars_5914_: *mut LeanObject,
    mut v_fields_5915_: *mut LeanObject,
    mut v_retTy_5916_: *mut LeanObject,
    mut v___y_5917_: *mut LeanObject,
    mut v___y_5918_: *mut LeanObject,
    mut v___y_5919_: *mut LeanObject,
    mut v___y_5920_: *mut LeanObject,
    mut v___y_5921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___y_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: u8 = 0;
    let mut v___x_5941_: u8 = 0;
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5946_: u8 = 0;
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5952_: u8 = 0;
    let mut v_a_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5956_: u8 = 0;
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5960_: u8 = 0;
    let mut v___x_5961_: u8 = 0;
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_head_5910_);
                v___x_5923_ = l_Lean_Elab_ComputedFields_isScalarField(
                    v_head_5910_,
                    v___y_5920_,
                    v___y_5921_,
                );
                if lean_obj_tag(v___x_5923_) == 0 {
                    v_a_5924_ = lean_ctor_get(v___x_5923_, 0);
                    lean_inc(v_a_5924_);
                    lean_dec_ref_known(v___x_5923_, 1);
                    v_nargs_5925_ = l_Lean_Expr_getAppNumArgs(v_retTy_5916_);
                    v___x_5926_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1;
                    v___x_5927_ = l_Lean_Name_append(v_name_5911_, v___x_5926_);
                    v___x_5928_ = l_Lean_mkConst(v___x_5927_, v_lparams_5912_);
                    v_dummy_5929_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once
                        ),
                        _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4,
                    );
                    lean_inc(v_nargs_5925_);
                    v___x_5930_ = lean_mk_array(v_nargs_5925_, v_dummy_5929_);
                    v___x_5931_ = lean_unsigned_to_nat(1);
                    v___x_5932_ = lean_nat_sub(v_nargs_5925_, v___x_5931_);
                    lean_dec(v_nargs_5925_);
                    v___x_5933_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_retTy_5916_,
                        v___x_5930_,
                        v___x_5932_,
                    );
                    v___x_5934_ = l_Lean_mkAppN(v___x_5928_, v___x_5933_);
                    lean_dec_ref(v___x_5933_);
                    v___x_5935_ = 1;
                    v___x_5961_ = (lean_unbox(v_a_5924_) as u8);
                    lean_dec(v_a_5924_);
                    if v___x_5961_ == 0 {
                        v___y_5937_ = v_compFieldVars_5914_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5962_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2;
                        v___y_5937_ = v___x_5962_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_retTy_5916_);
                    lean_dec_ref(v_params_5913_);
                    lean_dec(v_lparams_5912_);
                    lean_dec(v_name_5911_);
                    lean_dec(v_head_5910_);
                    v_a_5963_ = lean_ctor_get(v___x_5923_, 0);
                    v_isSharedCheck_5970_ = (!lean_is_exclusive(v___x_5923_)) as u8;
                    if v_isSharedCheck_5970_ == 0 {
                        v___x_5965_ = v___x_5923_;
                        v_isShared_5966_ = v_isSharedCheck_5970_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5963_);
                        lean_dec(v___x_5923_);
                        v___x_5965_ = lean_box(0);
                        v_isShared_5966_ = v_isSharedCheck_5970_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5938_ = l_Array_append___redArg(v_params_5913_, v___y_5937_);
                v___x_5939_ = l_Array_append___redArg(v___x_5938_, v_fields_5915_);
                v___x_5940_ = 0;
                v___x_5941_ = 1;
                v___x_5942_ = l_Lean_Meta_mkForallFVars(
                    v___x_5939_,
                    v___x_5934_,
                    v___x_5940_,
                    v___x_5935_,
                    v___x_5935_,
                    v___x_5941_,
                    v___y_5918_,
                    v___y_5919_,
                    v___y_5920_,
                    v___y_5921_,
                );
                lean_dec_ref(v___x_5939_);
                if lean_obj_tag(v___x_5942_) == 0 {
                    v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
                    v_isSharedCheck_5952_ = (!lean_is_exclusive(v___x_5942_)) as u8;
                    if v_isSharedCheck_5952_ == 0 {
                        v___x_5945_ = v___x_5942_;
                        v_isShared_5946_ = v_isSharedCheck_5952_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5943_);
                        lean_dec(v___x_5942_);
                        v___x_5945_ = lean_box(0);
                        v_isShared_5946_ = v_isSharedCheck_5952_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_head_5910_);
                    v_a_5953_ = lean_ctor_get(v___x_5942_, 0);
                    v_isSharedCheck_5960_ = (!lean_is_exclusive(v___x_5942_)) as u8;
                    if v_isSharedCheck_5960_ == 0 {
                        v___x_5955_ = v___x_5942_;
                        v_isShared_5956_ = v_isSharedCheck_5960_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5953_);
                        lean_dec(v___x_5942_);
                        v___x_5955_ = lean_box(0);
                        v_isShared_5956_ = v_isSharedCheck_5960_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5947_ = l_Lean_Name_append(v_head_5910_, v___x_5926_);
                v___x_5948_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5948_, 0, v___x_5947_);
                lean_ctor_set(v___x_5948_, 1, v_a_5943_);
                if v_isShared_5946_ == 0 {
                    lean_ctor_set(v___x_5945_, 0, v___x_5948_);
                    v___x_5950_ = v___x_5945_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5951_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5951_, 0, v___x_5948_);
                    v___x_5950_ = v_reuseFailAlloc_5951_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5950_;
            }
            4 => {
                if v_isShared_5956_ == 0 {
                    v___x_5958_ = v___x_5955_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_a_5953_);
                    v___x_5958_ = v_reuseFailAlloc_5959_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5958_;
            }
            6 => {
                if v_isShared_5966_ == 0 {
                    v___x_5968_ = v___x_5965_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
                    v___x_5968_ = v_reuseFailAlloc_5969_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(
    mut v_head_5971_: *mut LeanObject,
    mut v_name_5972_: *mut LeanObject,
    mut v_lparams_5973_: *mut LeanObject,
    mut v_params_5974_: *mut LeanObject,
    mut v_compFieldVars_5975_: *mut LeanObject,
    mut v_fields_5976_: *mut LeanObject,
    mut v_retTy_5977_: *mut LeanObject,
    mut v___y_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5984_: *mut LeanObject = core::ptr::null_mut();
    v_res_5984_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(
        v_head_5971_,
        v_name_5972_,
        v_lparams_5973_,
        v_params_5974_,
        v_compFieldVars_5975_,
        v_fields_5976_,
        v_retTy_5977_,
        v___y_5978_,
        v___y_5979_,
        v___y_5980_,
        v___y_5981_,
        v___y_5982_,
    );
    lean_dec(v___y_5982_);
    lean_dec_ref(v___y_5981_);
    lean_dec(v___y_5980_);
    lean_dec_ref(v___y_5979_);
    lean_dec_ref(v___y_5978_);
    lean_dec_ref(v_fields_5976_);
    lean_dec_ref(v_compFieldVars_5975_);
    return v_res_5984_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(
    mut v_name_5985_: *mut LeanObject,
    mut v_lparams_5986_: *mut LeanObject,
    mut v_params_5987_: *mut LeanObject,
    mut v_compFieldVars_5988_: *mut LeanObject,
    mut v_x_5989_: *mut LeanObject,
    mut v_x_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6003_: u8 = 0;
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: u8 = 0;
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6019_: u8 = 0;
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut v_a_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v_isSharedCheck_6032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5989_) == 0 {
                    lean_dec_ref(v_compFieldVars_5988_);
                    lean_dec_ref(v_params_5987_);
                    lean_dec(v_lparams_5986_);
                    lean_dec(v_name_5985_);
                    v___x_5997_ = l_List_reverse___redArg(v_x_5990_);
                    v___x_5998_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5998_, 0, v___x_5997_);
                    return v___x_5998_;
                } else {
                    v_head_5999_ = lean_ctor_get(v_x_5989_, 0);
                    v_tail_6000_ = lean_ctor_get(v_x_5989_, 1);
                    v_isSharedCheck_6032_ = (!lean_is_exclusive(v_x_5989_)) as u8;
                    if v_isSharedCheck_6032_ == 0 {
                        v___x_6002_ = v_x_5989_;
                        v_isShared_6003_ = v_isSharedCheck_6032_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6000_);
                        lean_inc(v_head_5999_);
                        lean_dec(v_x_5989_);
                        v___x_6002_ = lean_box(0);
                        v_isShared_6003_ = v_isSharedCheck_6032_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_lparams_5986_);
                lean_inc(v_head_5999_);
                v___x_6004_ = l_Lean_mkConst(v_head_5999_, v_lparams_5986_);
                v___x_6005_ = l_Lean_mkAppN(v___x_6004_, v_params_5987_);
                lean_inc(v___y_5995_);
                lean_inc_ref(v___y_5994_);
                lean_inc(v___y_5993_);
                lean_inc_ref(v___y_5992_);
                v___x_6006_ = lean_infer_type(
                    v___x_6005_,
                    v___y_5992_,
                    v___y_5993_,
                    v___y_5994_,
                    v___y_5995_,
                );
                if lean_obj_tag(v___x_6006_) == 0 {
                    v_a_6007_ = lean_ctor_get(v___x_6006_, 0);
                    lean_inc(v_a_6007_);
                    lean_dec_ref_known(v___x_6006_, 1);
                    lean_inc_ref(v_compFieldVars_5988_);
                    lean_inc_ref(v_params_5987_);
                    lean_inc(v_lparams_5986_);
                    lean_inc(v_name_5985_);
                    v___f_6008_ = lean_alloc_closure(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed as *mut core::ffi::c_void, 13, 5);
                    lean_closure_set(v___f_6008_, 0, v_head_5999_);
                    lean_closure_set(v___f_6008_, 1, v_name_5985_);
                    lean_closure_set(v___f_6008_, 2, v_lparams_5986_);
                    lean_closure_set(v___f_6008_, 3, v_params_5987_);
                    lean_closure_set(v___f_6008_, 4, v_compFieldVars_5988_);
                    v___x_6009_ = 0;
                    v___x_6010_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_6007_, v___f_6008_, v___x_6009_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
                    if lean_obj_tag(v___x_6010_) == 0 {
                        v_a_6011_ = lean_ctor_get(v___x_6010_, 0);
                        lean_inc(v_a_6011_);
                        lean_dec_ref_known(v___x_6010_, 1);
                        if v_isShared_6003_ == 0 {
                            lean_ctor_set(v___x_6002_, 1, v_x_5990_);
                            lean_ctor_set(v___x_6002_, 0, v_a_6011_);
                            v___x_6013_ = v___x_6002_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6015_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_a_6011_);
                            lean_ctor_set(v_reuseFailAlloc_6015_, 1, v_x_5990_);
                            v___x_6013_ = v_reuseFailAlloc_6015_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6002_);
                        lean_dec(v_tail_6000_);
                        lean_dec(v_x_5990_);
                        lean_dec_ref(v_compFieldVars_5988_);
                        lean_dec_ref(v_params_5987_);
                        lean_dec(v_lparams_5986_);
                        lean_dec(v_name_5985_);
                        v_a_6016_ = lean_ctor_get(v___x_6010_, 0);
                        v_isSharedCheck_6023_ = (!lean_is_exclusive(v___x_6010_)) as u8;
                        if v_isSharedCheck_6023_ == 0 {
                            v___x_6018_ = v___x_6010_;
                            v_isShared_6019_ = v_isSharedCheck_6023_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6016_);
                            lean_dec(v___x_6010_);
                            v___x_6018_ = lean_box(0);
                            v_isShared_6019_ = v_isSharedCheck_6023_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6002_);
                    lean_dec(v_tail_6000_);
                    lean_dec(v_head_5999_);
                    lean_dec(v_x_5990_);
                    lean_dec_ref(v_compFieldVars_5988_);
                    lean_dec_ref(v_params_5987_);
                    lean_dec(v_lparams_5986_);
                    lean_dec(v_name_5985_);
                    v_a_6024_ = lean_ctor_get(v___x_6006_, 0);
                    v_isSharedCheck_6031_ = (!lean_is_exclusive(v___x_6006_)) as u8;
                    if v_isSharedCheck_6031_ == 0 {
                        v___x_6026_ = v___x_6006_;
                        v_isShared_6027_ = v_isSharedCheck_6031_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6024_);
                        lean_dec(v___x_6006_);
                        v___x_6026_ = lean_box(0);
                        v_isShared_6027_ = v_isSharedCheck_6031_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_x_5989_ = v_tail_6000_;
                v_x_5990_ = v___x_6013_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6019_ == 0 {
                    v___x_6021_ = v___x_6018_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6016_);
                    v___x_6021_ = v_reuseFailAlloc_6022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6021_;
            }
            5 => {
                if v_isShared_6027_ == 0 {
                    v___x_6029_ = v___x_6026_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
                    v___x_6029_ = v_reuseFailAlloc_6030_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(
    mut v_name_6033_: *mut LeanObject,
    mut v_lparams_6034_: *mut LeanObject,
    mut v_params_6035_: *mut LeanObject,
    mut v_compFieldVars_6036_: *mut LeanObject,
    mut v_x_6037_: *mut LeanObject,
    mut v_x_6038_: *mut LeanObject,
    mut v___y_6039_: *mut LeanObject,
    mut v___y_6040_: *mut LeanObject,
    mut v___y_6041_: *mut LeanObject,
    mut v___y_6042_: *mut LeanObject,
    mut v___y_6043_: *mut LeanObject,
    mut v___y_6044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6045_: *mut LeanObject = core::ptr::null_mut();
    v_res_6045_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(
        v_name_6033_,
        v_lparams_6034_,
        v_params_6035_,
        v_compFieldVars_6036_,
        v_x_6037_,
        v_x_6038_,
        v___y_6039_,
        v___y_6040_,
        v___y_6041_,
        v___y_6042_,
        v___y_6043_,
    );
    lean_dec(v___y_6043_);
    lean_dec_ref(v___y_6042_);
    lean_dec(v___y_6041_);
    lean_dec_ref(v___y_6040_);
    lean_dec_ref(v___y_6039_);
    return v_res_6045_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkImplType(
    mut v_a_6046_: *mut LeanObject,
    mut v_a_6047_: *mut LeanObject,
    mut v_a_6048_: *mut LeanObject,
    mut v_a_6049_: *mut LeanObject,
    mut v_a_6050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInductiveVal_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lparams_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_compFieldVars_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_6059_: u8 = 0;
    let mut v_name_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: u8 = 0;
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6076_: u8 = 0;
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInductiveVal_6052_ = lean_ctor_get(v_a_6046_, 0);
                v_toConstantVal_6053_ = lean_ctor_get(v_toInductiveVal_6052_, 0);
                v_lparams_6054_ = lean_ctor_get(v_a_6046_, 1);
                v_params_6055_ = lean_ctor_get(v_a_6046_, 2);
                v_compFieldVars_6056_ = lean_ctor_get(v_a_6046_, 4);
                v_numParams_6057_ = lean_ctor_get(v_toInductiveVal_6052_, 1);
                v_ctors_6058_ = lean_ctor_get(v_toInductiveVal_6052_, 4);
                v_isUnsafe_6059_ = lean_ctor_get_uint8(
                    v_toInductiveVal_6052_,
                    (core::mem::size_of::<*mut LeanObject>() * 6 + 1) as u32,
                );
                v_name_6060_ = lean_ctor_get(v_toConstantVal_6053_, 0);
                v_levelParams_6061_ = lean_ctor_get(v_toConstantVal_6053_, 1);
                v_type_6062_ = lean_ctor_get(v_toConstantVal_6053_, 2);
                v___x_6063_ = lean_box(0);
                lean_inc(v_ctors_6058_);
                lean_inc_ref(v_compFieldVars_6056_);
                lean_inc_ref(v_params_6055_);
                lean_inc(v_lparams_6054_);
                lean_inc(v_name_6060_);
                v___x_6064_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(
                    v_name_6060_,
                    v_lparams_6054_,
                    v_params_6055_,
                    v_compFieldVars_6056_,
                    v_ctors_6058_,
                    v___x_6063_,
                    v_a_6046_,
                    v_a_6047_,
                    v_a_6048_,
                    v_a_6049_,
                    v_a_6050_,
                );
                if lean_obj_tag(v___x_6064_) == 0 {
                    v_a_6065_ = lean_ctor_get(v___x_6064_, 0);
                    lean_inc(v_a_6065_);
                    lean_dec_ref_known(v___x_6064_, 1);
                    v___x_6066_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1;
                    lean_inc(v_name_6060_);
                    v___x_6067_ = l_Lean_Name_append(v_name_6060_, v___x_6066_);
                    lean_inc_ref(v_type_6062_);
                    v___x_6068_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_6068_, 0, v___x_6067_);
                    lean_ctor_set(v___x_6068_, 1, v_type_6062_);
                    lean_ctor_set(v___x_6068_, 2, v_a_6065_);
                    v___x_6069_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6069_, 0, v___x_6068_);
                    lean_ctor_set(v___x_6069_, 1, v___x_6063_);
                    lean_inc(v_numParams_6057_);
                    lean_inc(v_levelParams_6061_);
                    v___x_6070_ = lean_alloc_ctor(6, 3, (1) as u32);
                    lean_ctor_set(v___x_6070_, 0, v_levelParams_6061_);
                    lean_ctor_set(v___x_6070_, 1, v_numParams_6057_);
                    lean_ctor_set(v___x_6070_, 2, v___x_6069_);
                    lean_ctor_set_uint8(
                        v___x_6070_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_isUnsafe_6059_,
                    );
                    v___x_6071_ = 0;
                    v___x_6072_ = l_Lean_addDecl(v___x_6070_, v___x_6071_, v_a_6049_, v_a_6050_);
                    return v___x_6072_;
                } else {
                    v_a_6073_ = lean_ctor_get(v___x_6064_, 0);
                    v_isSharedCheck_6080_ = (!lean_is_exclusive(v___x_6064_)) as u8;
                    if v_isSharedCheck_6080_ == 0 {
                        v___x_6075_ = v___x_6064_;
                        v_isShared_6076_ = v_isSharedCheck_6080_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6073_);
                        lean_dec(v___x_6064_);
                        v___x_6075_ = lean_box(0);
                        v_isShared_6076_ = v_isSharedCheck_6080_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6076_ == 0 {
                    v___x_6078_ = v___x_6075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_a_6073_);
                    v___x_6078_ = v_reuseFailAlloc_6079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkImplType___boxed(
    mut v_a_6081_: *mut LeanObject,
    mut v_a_6082_: *mut LeanObject,
    mut v_a_6083_: *mut LeanObject,
    mut v_a_6084_: *mut LeanObject,
    mut v_a_6085_: *mut LeanObject,
    mut v_a_6086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6087_: *mut LeanObject = core::ptr::null_mut();
    v_res_6087_ = l_Lean_Elab_ComputedFields_mkImplType(
        v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_,
    );
    lean_dec(v_a_6085_);
    lean_dec_ref(v_a_6084_);
    lean_dec(v_a_6083_);
    lean_dec_ref(v_a_6082_);
    lean_dec_ref(v_a_6081_);
    return v_res_6087_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(
    mut v_k_6088_: *mut LeanObject,
    mut v___y_6089_: *mut LeanObject,
    mut v_b_6090_: *mut LeanObject,
    mut v___y_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_6094_);
    lean_inc_ref(v___y_6093_);
    lean_inc(v___y_6092_);
    lean_inc_ref(v___y_6091_);
    lean_inc_ref(v___y_6089_);
    v___x_6096_ = lean_apply_7(
        v_k_6088_,
        v_b_6090_,
        v___y_6089_,
        v___y_6091_,
        v___y_6092_,
        v___y_6093_,
        v___y_6094_,
        lean_box(0),
    );
    return v___x_6096_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(
    mut v_k_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
    mut v_b_6099_: *mut LeanObject,
    mut v___y_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
    mut v___y_6104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6105_: *mut LeanObject = core::ptr::null_mut();
    v_res_6105_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_6097_, v___y_6098_, v_b_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_);
    lean_dec(v___y_6103_);
    lean_dec_ref(v___y_6102_);
    lean_dec(v___y_6101_);
    lean_dec_ref(v___y_6100_);
    lean_dec_ref(v___y_6098_);
    return v_res_6105_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(
    mut v_name_6106_: *mut LeanObject,
    mut v_type_6107_: *mut LeanObject,
    mut v_val_6108_: *mut LeanObject,
    mut v_k_6109_: *mut LeanObject,
    mut v_nondep_6110_: u8,
    mut v_kind_6111_: u8,
    mut v___y_6112_: *mut LeanObject,
    mut v___y_6113_: *mut LeanObject,
    mut v___y_6114_: *mut LeanObject,
    mut v___y_6115_: *mut LeanObject,
    mut v___y_6116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_6112_);
                v___f_6118_ = lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_6118_, 0, v_k_6109_);
                lean_closure_set(v___f_6118_, 1, v___y_6112_);
                v___x_6119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
                    v_name_6106_,
                    v_type_6107_,
                    v_val_6108_,
                    v___f_6118_,
                    v_nondep_6110_,
                    v_kind_6111_,
                    v___y_6113_,
                    v___y_6114_,
                    v___y_6115_,
                    v___y_6116_,
                );
                if lean_obj_tag(v___x_6119_) == 0 {
                    return v___x_6119_;
                } else {
                    v_a_6120_ = lean_ctor_get(v___x_6119_, 0);
                    v_isSharedCheck_6127_ = (!lean_is_exclusive(v___x_6119_)) as u8;
                    if v_isSharedCheck_6127_ == 0 {
                        v___x_6122_ = v___x_6119_;
                        v_isShared_6123_ = v_isSharedCheck_6127_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6120_);
                        lean_dec(v___x_6119_);
                        v___x_6122_ = lean_box(0);
                        v_isShared_6123_ = v_isSharedCheck_6127_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6123_ == 0 {
                    v___x_6125_ = v___x_6122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_a_6120_);
                    v___x_6125_ = v_reuseFailAlloc_6126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(
    mut v_name_6128_: *mut LeanObject,
    mut v_type_6129_: *mut LeanObject,
    mut v_val_6130_: *mut LeanObject,
    mut v_k_6131_: *mut LeanObject,
    mut v_nondep_6132_: *mut LeanObject,
    mut v_kind_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
    mut v___y_6135_: *mut LeanObject,
    mut v___y_6136_: *mut LeanObject,
    mut v___y_6137_: *mut LeanObject,
    mut v___y_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_6140_: u8 = 0;
    let mut v_kind_boxed_6141_: u8 = 0;
    let mut v_res_6142_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6140_ = (lean_unbox(v_nondep_6132_) as u8);
    v_kind_boxed_6141_ = (lean_unbox(v_kind_6133_) as u8);
    v_res_6142_ =
        l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(
            v_name_6128_,
            v_type_6129_,
            v_val_6130_,
            v_k_6131_,
            v_nondep_boxed_6140_,
            v_kind_boxed_6141_,
            v___y_6134_,
            v___y_6135_,
            v___y_6136_,
            v___y_6137_,
            v___y_6138_,
        );
    lean_dec(v___y_6138_);
    lean_dec_ref(v___y_6137_);
    lean_dec(v___y_6136_);
    lean_dec_ref(v___y_6135_);
    lean_dec_ref(v___y_6134_);
    return v_res_6142_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(
    mut v_00_u03b1_6143_: *mut LeanObject,
    mut v_name_6144_: *mut LeanObject,
    mut v_type_6145_: *mut LeanObject,
    mut v_val_6146_: *mut LeanObject,
    mut v_k_6147_: *mut LeanObject,
    mut v_nondep_6148_: u8,
    mut v_kind_6149_: u8,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    v___x_6156_ =
        l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(
            v_name_6144_,
            v_type_6145_,
            v_val_6146_,
            v_k_6147_,
            v_nondep_6148_,
            v_kind_6149_,
            v___y_6150_,
            v___y_6151_,
            v___y_6152_,
            v___y_6153_,
            v___y_6154_,
        );
    return v___x_6156_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(
    mut v_00_u03b1_6157_: *mut LeanObject,
    mut v_name_6158_: *mut LeanObject,
    mut v_type_6159_: *mut LeanObject,
    mut v_val_6160_: *mut LeanObject,
    mut v_k_6161_: *mut LeanObject,
    mut v_nondep_6162_: *mut LeanObject,
    mut v_kind_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
    mut v___y_6169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_6170_: u8 = 0;
    let mut v_kind_boxed_6171_: u8 = 0;
    let mut v_res_6172_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6170_ = (lean_unbox(v_nondep_6162_) as u8);
    v_kind_boxed_6171_ = (lean_unbox(v_kind_6163_) as u8);
    v_res_6172_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(
        v_00_u03b1_6157_,
        v_name_6158_,
        v_type_6159_,
        v_val_6160_,
        v_k_6161_,
        v_nondep_boxed_6170_,
        v_kind_boxed_6171_,
        v___y_6164_,
        v___y_6165_,
        v___y_6166_,
        v___y_6167_,
        v___y_6168_,
    );
    lean_dec(v___y_6168_);
    lean_dec_ref(v___y_6167_);
    lean_dec(v___y_6166_);
    lean_dec_ref(v___y_6165_);
    lean_dec_ref(v___y_6164_);
    return v_res_6172_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(
    mut v___x_6173_: *mut LeanObject,
    mut v___x_6174_: *mut LeanObject,
    mut v_majorImpl_6175_: *mut LeanObject,
    mut v_m_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: u8 = 0;
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: u8 = 0;
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    v___x_6183_ = lean_mk_empty_array_with_capacity(v___x_6173_);
    lean_inc_ref(v_m_6176_);
    lean_inc_ref(v___x_6183_);
    v___x_6184_ = lean_array_push(v___x_6183_, v_m_6176_);
    v___x_6185_ = l_Array_append___redArg(v___x_6184_, v___x_6174_);
    v___x_6186_ = lean_array_push(v___x_6183_, v_majorImpl_6175_);
    v___x_6187_ = l_Array_append___redArg(v___x_6185_, v___x_6186_);
    lean_dec_ref(v___x_6186_);
    v___x_6188_ = 0;
    v___x_6189_ = 1;
    v___x_6190_ = 1;
    v___x_6191_ = l_Lean_Meta_mkLambdaFVars(
        v___x_6187_,
        v_m_6176_,
        v___x_6188_,
        v___x_6189_,
        v___x_6188_,
        v___x_6189_,
        v___x_6190_,
        v___y_6178_,
        v___y_6179_,
        v___y_6180_,
        v___y_6181_,
    );
    lean_dec_ref(v___x_6187_);
    return v___x_6191_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(
    mut v___x_6192_: *mut LeanObject,
    mut v___x_6193_: *mut LeanObject,
    mut v_majorImpl_6194_: *mut LeanObject,
    mut v_m_6195_: *mut LeanObject,
    mut v___y_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6202_: *mut LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(
        v___x_6192_,
        v___x_6193_,
        v_majorImpl_6194_,
        v_m_6195_,
        v___y_6196_,
        v___y_6197_,
        v___y_6198_,
        v___y_6199_,
        v___y_6200_,
    );
    lean_dec(v___y_6200_);
    lean_dec_ref(v___y_6199_);
    lean_dec(v___y_6198_);
    lean_dec_ref(v___y_6197_);
    lean_dec_ref(v___y_6196_);
    lean_dec_ref(v___x_6193_);
    lean_dec(v___x_6192_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(
    mut v_constMotive_6206_: *mut LeanObject,
    mut v___x_6207_: *mut LeanObject,
    mut v___x_6208_: *mut LeanObject,
    mut v_majorImpl_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
    mut v___y_6214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_6214_);
    lean_inc_ref(v___y_6213_);
    lean_inc(v___y_6212_);
    lean_inc_ref(v___y_6211_);
    lean_inc_ref(v_constMotive_6206_);
    v___x_6216_ = lean_infer_type(
        v_constMotive_6206_,
        v___y_6211_,
        v___y_6212_,
        v___y_6213_,
        v___y_6214_,
    );
    if lean_obj_tag(v___x_6216_) == 0 {
        let mut v_a_6217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6220_: u8 = 0;
        let mut v___x_6221_: u8 = 0;
        let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
        v_a_6217_ = lean_ctor_get(v___x_6216_, 0);
        lean_inc(v_a_6217_);
        lean_dec_ref_known(v___x_6216_, 1);
        v___f_6218_ = lean_alloc_closure(
            l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed as *mut core::ffi::c_void,
            10,
            3,
        );
        lean_closure_set(v___f_6218_, 0, v___x_6207_);
        lean_closure_set(v___f_6218_, 1, v___x_6208_);
        lean_closure_set(v___f_6218_, 2, v_majorImpl_6209_);
        v___x_6219_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1;
        v___x_6220_ = 0;
        v___x_6221_ = 0;
        v___x_6222_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_6219_, v_a_6217_, v_constMotive_6206_, v___f_6218_, v___x_6220_, v___x_6221_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_);
        return v___x_6222_;
    } else {
        lean_dec_ref(v_majorImpl_6209_);
        lean_dec_ref(v___x_6208_);
        lean_dec(v___x_6207_);
        lean_dec_ref(v_constMotive_6206_);
        return v___x_6216_;
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(
    mut v_constMotive_6223_: *mut LeanObject,
    mut v___x_6224_: *mut LeanObject,
    mut v___x_6225_: *mut LeanObject,
    mut v_majorImpl_6226_: *mut LeanObject,
    mut v___y_6227_: *mut LeanObject,
    mut v___y_6228_: *mut LeanObject,
    mut v___y_6229_: *mut LeanObject,
    mut v___y_6230_: *mut LeanObject,
    mut v___y_6231_: *mut LeanObject,
    mut v___y_6232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6233_: *mut LeanObject = core::ptr::null_mut();
    v_res_6233_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(
        v_constMotive_6223_,
        v___x_6224_,
        v___x_6225_,
        v_majorImpl_6226_,
        v___y_6227_,
        v___y_6228_,
        v___y_6229_,
        v___y_6230_,
        v___y_6231_,
    );
    lean_dec(v___y_6231_);
    lean_dec_ref(v___y_6230_);
    lean_dec(v___y_6229_);
    lean_dec_ref(v___y_6228_);
    lean_dec_ref(v___y_6227_);
    return v_res_6233_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(
    mut v_name_6234_: *mut LeanObject,
    mut v_bi_6235_: u8,
    mut v_type_6236_: *mut LeanObject,
    mut v_k_6237_: *mut LeanObject,
    mut v_kind_6238_: u8,
    mut v___y_6239_: *mut LeanObject,
    mut v___y_6240_: *mut LeanObject,
    mut v___y_6241_: *mut LeanObject,
    mut v___y_6242_: *mut LeanObject,
    mut v___y_6243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6250_: u8 = 0;
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_6239_);
                v___f_6245_ = lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_6245_, 0, v_k_6237_);
                lean_closure_set(v___f_6245_, 1, v___y_6239_);
                v___x_6246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_6234_,
                    v_bi_6235_,
                    v_type_6236_,
                    v___f_6245_,
                    v_kind_6238_,
                    v___y_6240_,
                    v___y_6241_,
                    v___y_6242_,
                    v___y_6243_,
                );
                if lean_obj_tag(v___x_6246_) == 0 {
                    return v___x_6246_;
                } else {
                    v_a_6247_ = lean_ctor_get(v___x_6246_, 0);
                    v_isSharedCheck_6254_ = (!lean_is_exclusive(v___x_6246_)) as u8;
                    if v_isSharedCheck_6254_ == 0 {
                        v___x_6249_ = v___x_6246_;
                        v_isShared_6250_ = v_isSharedCheck_6254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6247_);
                        lean_dec(v___x_6246_);
                        v___x_6249_ = lean_box(0);
                        v_isShared_6250_ = v_isSharedCheck_6254_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6250_ == 0 {
                    v___x_6252_ = v___x_6249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6253_, 0, v_a_6247_);
                    v___x_6252_ = v_reuseFailAlloc_6253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(
    mut v_name_6255_: *mut LeanObject,
    mut v_bi_6256_: *mut LeanObject,
    mut v_type_6257_: *mut LeanObject,
    mut v_k_6258_: *mut LeanObject,
    mut v_kind_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
    mut v___y_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
    mut v___y_6264_: *mut LeanObject,
    mut v___y_6265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_6266_: u8 = 0;
    let mut v_kind_boxed_6267_: u8 = 0;
    let mut v_res_6268_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_6266_ = (lean_unbox(v_bi_6256_) as u8);
    v_kind_boxed_6267_ = (lean_unbox(v_kind_6259_) as u8);
    v_res_6268_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_6255_, v_bi_boxed_6266_, v_type_6257_, v_k_6258_, v_kind_boxed_6267_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_);
    lean_dec(v___y_6264_);
    lean_dec_ref(v___y_6263_);
    lean_dec(v___y_6262_);
    lean_dec_ref(v___y_6261_);
    lean_dec_ref(v___y_6260_);
    return v_res_6268_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(
    mut v_name_6269_: *mut LeanObject,
    mut v_type_6270_: *mut LeanObject,
    mut v_k_6271_: *mut LeanObject,
    mut v___y_6272_: *mut LeanObject,
    mut v___y_6273_: *mut LeanObject,
    mut v___y_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6278_: u8 = 0;
    let mut v___x_6279_: u8 = 0;
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    v___x_6278_ = 0;
    v___x_6279_ = 0;
    v___x_6280_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_6269_, v___x_6278_, v_type_6270_, v_k_6271_, v___x_6279_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_);
    return v___x_6280_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(
    mut v_name_6281_: *mut LeanObject,
    mut v_type_6282_: *mut LeanObject,
    mut v_k_6283_: *mut LeanObject,
    mut v___y_6284_: *mut LeanObject,
    mut v___y_6285_: *mut LeanObject,
    mut v___y_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
    mut v___y_6289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6290_: *mut LeanObject = core::ptr::null_mut();
    v_res_6290_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_6281_, v_type_6282_, v_k_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
    lean_dec(v___y_6288_);
    lean_dec_ref(v___y_6287_);
    lean_dec(v___y_6286_);
    lean_dec_ref(v___y_6285_);
    lean_dec_ref(v___y_6284_);
    return v_res_6290_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(
    mut v_a_6291_: *mut LeanObject,
    mut v_a_6292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6298_: u8 = 0;
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6291_) == 0 {
                    v___x_6293_ = l_List_reverse___redArg(v_a_6292_);
                    return v___x_6293_;
                } else {
                    v_head_6294_ = lean_ctor_get(v_a_6291_, 0);
                    v_tail_6295_ = lean_ctor_get(v_a_6291_, 1);
                    v_isSharedCheck_6304_ = (!lean_is_exclusive(v_a_6291_)) as u8;
                    if v_isSharedCheck_6304_ == 0 {
                        v___x_6297_ = v_a_6291_;
                        v_isShared_6298_ = v_isSharedCheck_6304_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6295_);
                        lean_inc(v_head_6294_);
                        lean_dec(v_a_6291_);
                        v___x_6297_ = lean_box(0);
                        v_isShared_6298_ = v_isSharedCheck_6304_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6299_ = l_Lean_mkLevelParam(v_head_6294_);
                if v_isShared_6298_ == 0 {
                    lean_ctor_set(v___x_6297_, 1, v_a_6292_);
                    lean_ctor_set(v___x_6297_, 0, v___x_6299_);
                    v___x_6301_ = v___x_6297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6303_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6303_, 0, v___x_6299_);
                    lean_ctor_set(v_reuseFailAlloc_6303_, 1, v_a_6292_);
                    v___x_6301_ = v_reuseFailAlloc_6303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6291_ = v_tail_6295_;
                v_a_6292_ = v___x_6301_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(
    mut v_a_6305_: *mut LeanObject,
    mut v_b_6306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6312_: u8 = 0;
    let mut v___x_6313_: u8 = 0;
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_6307_ = lean_ctor_get(v_a_6305_, 0);
                v_start_6308_ = lean_ctor_get(v_a_6305_, 1);
                v_stop_6309_ = lean_ctor_get(v_a_6305_, 2);
                v_isSharedCheck_6322_ = (!lean_is_exclusive(v_a_6305_)) as u8;
                if v_isSharedCheck_6322_ == 0 {
                    v___x_6311_ = v_a_6305_;
                    v_isShared_6312_ = v_isSharedCheck_6322_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_6309_);
                    lean_inc(v_start_6308_);
                    lean_inc(v_array_6307_);
                    lean_dec(v_a_6305_);
                    v___x_6311_ = lean_box(0);
                    v_isShared_6312_ = v_isSharedCheck_6322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6313_ = lean_nat_dec_lt(v_start_6308_, v_stop_6309_);
                if v___x_6313_ == 0 {
                    lean_del_object(v___x_6311_);
                    lean_dec(v_stop_6309_);
                    lean_dec(v_start_6308_);
                    lean_dec_ref(v_array_6307_);
                    return v_b_6306_;
                } else {
                    v___x_6314_ = lean_unsigned_to_nat(1);
                    v___x_6315_ = lean_nat_add(v_start_6308_, v___x_6314_);
                    lean_inc_ref(v_array_6307_);
                    if v_isShared_6312_ == 0 {
                        lean_ctor_set(v___x_6311_, 1, v___x_6315_);
                        v___x_6317_ = v___x_6311_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6321_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6321_, 0, v_array_6307_);
                        lean_ctor_set(v_reuseFailAlloc_6321_, 1, v___x_6315_);
                        lean_ctor_set(v_reuseFailAlloc_6321_, 2, v_stop_6309_);
                        v___x_6317_ = v_reuseFailAlloc_6321_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6318_ = lean_array_fget(v_array_6307_, v_start_6308_);
                lean_dec(v_start_6308_);
                lean_dec_ref(v_array_6307_);
                v___x_6319_ = lean_array_push(v_b_6306_, v___x_6318_);
                v_a_6305_ = v___x_6317_;
                v_b_6306_ = v___x_6319_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(
    mut v_b_6323_: *mut LeanObject,
    mut v_a_6324_: *mut LeanObject,
    mut v_constMotive_6325_: *mut LeanObject,
    mut v___x_6326_: u8,
    mut v_compFieldVars_6327_: *mut LeanObject,
    mut v_args_6328_: *mut LeanObject,
    mut v_x_6329_: *mut LeanObject,
    mut v___y_6330_: *mut LeanObject,
    mut v___y_6331_: *mut LeanObject,
    mut v___y_6332_: *mut LeanObject,
    mut v___y_6333_: *mut LeanObject,
    mut v___y_6334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: u8 = 0;
    let mut v___x_6345_: u8 = 0;
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: u8 = 0;
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6352_: u8 = 0;
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6336_ =
                    l_Lean_Elab_ComputedFields_isScalarField(v_b_6323_, v___y_6333_, v___y_6334_);
                if lean_obj_tag(v___x_6336_) == 0 {
                    v_a_6337_ = lean_ctor_get(v___x_6336_, 0);
                    lean_inc(v_a_6337_);
                    lean_dec_ref_known(v___x_6336_, 1);
                    v___x_6338_ = l_Lean_mkAppN(v_a_6324_, v_args_6328_);
                    v___x_6339_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
                        v_constMotive_6325_,
                        v___x_6338_,
                        v___y_6331_,
                        v___y_6332_,
                        v___y_6333_,
                        v___y_6334_,
                    );
                    if lean_obj_tag(v___x_6339_) == 0 {
                        v_a_6340_ = lean_ctor_get(v___x_6339_, 0);
                        lean_inc(v_a_6340_);
                        lean_dec_ref_known(v___x_6339_, 1);
                        v___x_6347_ = (lean_unbox(v_a_6337_) as u8);
                        lean_dec(v_a_6337_);
                        if v___x_6347_ == 0 {
                            v___y_6342_ = v_compFieldVars_6327_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_compFieldVars_6327_);
                            v___x_6348_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2;
                            v___y_6342_ = v___x_6348_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_6337_);
                        lean_dec_ref(v_compFieldVars_6327_);
                        return v___x_6339_;
                    }
                } else {
                    lean_dec_ref(v_compFieldVars_6327_);
                    lean_dec_ref(v_constMotive_6325_);
                    lean_dec_ref(v_a_6324_);
                    v_a_6349_ = lean_ctor_get(v___x_6336_, 0);
                    v_isSharedCheck_6356_ = (!lean_is_exclusive(v___x_6336_)) as u8;
                    if v_isSharedCheck_6356_ == 0 {
                        v___x_6351_ = v___x_6336_;
                        v_isShared_6352_ = v_isSharedCheck_6356_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6349_);
                        lean_dec(v___x_6336_);
                        v___x_6351_ = lean_box(0);
                        v_isShared_6352_ = v_isSharedCheck_6356_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6343_ = l_Array_append___redArg(v___y_6342_, v_args_6328_);
                v___x_6344_ = 0;
                v___x_6345_ = 1;
                v___x_6346_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_6343_,
                    v_a_6340_,
                    v___x_6344_,
                    v___x_6326_,
                    v___x_6344_,
                    v___x_6326_,
                    v___x_6345_,
                    v___y_6331_,
                    v___y_6332_,
                    v___y_6333_,
                    v___y_6334_,
                );
                lean_dec_ref(v___x_6343_);
                return v___x_6346_;
            }
            2 => {
                if v_isShared_6352_ == 0 {
                    v___x_6354_ = v___x_6351_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_a_6349_);
                    v___x_6354_ = v_reuseFailAlloc_6355_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(
    mut v_b_6357_: *mut LeanObject,
    mut v_a_6358_: *mut LeanObject,
    mut v_constMotive_6359_: *mut LeanObject,
    mut v___x_6360_: *mut LeanObject,
    mut v_compFieldVars_6361_: *mut LeanObject,
    mut v_args_6362_: *mut LeanObject,
    mut v_x_6363_: *mut LeanObject,
    mut v___y_6364_: *mut LeanObject,
    mut v___y_6365_: *mut LeanObject,
    mut v___y_6366_: *mut LeanObject,
    mut v___y_6367_: *mut LeanObject,
    mut v___y_6368_: *mut LeanObject,
    mut v___y_6369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_12673__boxed_6370_: u8 = 0;
    let mut v_res_6371_: *mut LeanObject = core::ptr::null_mut();
    v___x_12673__boxed_6370_ = (lean_unbox(v___x_6360_) as u8);
    v_res_6371_ =
        l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(
            v_b_6357_,
            v_a_6358_,
            v_constMotive_6359_,
            v___x_12673__boxed_6370_,
            v_compFieldVars_6361_,
            v_args_6362_,
            v_x_6363_,
            v___y_6364_,
            v___y_6365_,
            v___y_6366_,
            v___y_6367_,
            v___y_6368_,
        );
    lean_dec(v___y_6368_);
    lean_dec_ref(v___y_6367_);
    lean_dec(v___y_6366_);
    lean_dec_ref(v___y_6365_);
    lean_dec_ref(v___y_6364_);
    lean_dec_ref(v_x_6363_);
    lean_dec_ref(v_args_6362_);
    return v_res_6371_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(
    mut v_constMotive_6372_: *mut LeanObject,
    mut v_compFieldVars_6373_: *mut LeanObject,
    mut v_as_6374_: *mut LeanObject,
    mut v_bs_6375_: *mut LeanObject,
    mut v_i_6376_: *mut LeanObject,
    mut v_cs_6377_: *mut LeanObject,
    mut v___y_6378_: *mut LeanObject,
    mut v___y_6379_: *mut LeanObject,
    mut v___y_6380_: *mut LeanObject,
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6394_: u8 = 0;
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6398_: u8 = 0;
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: u8 = 0;
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: u8 = 0;
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: u8 = 0;
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6399_ = lean_array_get_size(v_as_6374_);
                v___x_6400_ = lean_nat_dec_lt(v_i_6376_, v___x_6399_);
                if v___x_6400_ == 0 {
                    lean_dec(v_i_6376_);
                    lean_dec_ref(v_compFieldVars_6373_);
                    lean_dec_ref(v_constMotive_6372_);
                    v___x_6401_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6401_, 0, v_cs_6377_);
                    return v___x_6401_;
                } else {
                    v___x_6402_ = lean_array_get_size(v_bs_6375_);
                    v___x_6403_ = lean_nat_dec_lt(v_i_6376_, v___x_6402_);
                    if v___x_6403_ == 0 {
                        lean_dec(v_i_6376_);
                        lean_dec_ref(v_compFieldVars_6373_);
                        lean_dec_ref(v_constMotive_6372_);
                        v___x_6404_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6404_, 0, v_cs_6377_);
                        return v___x_6404_;
                    } else {
                        v_a_6405_ = lean_array_fget_borrowed(v_as_6374_, v_i_6376_);
                        lean_inc(v___y_6382_);
                        lean_inc_ref(v___y_6381_);
                        lean_inc(v___y_6380_);
                        lean_inc_ref(v___y_6379_);
                        lean_inc(v_a_6405_);
                        v___x_6406_ = lean_infer_type(
                            v_a_6405_,
                            v___y_6379_,
                            v___y_6380_,
                            v___y_6381_,
                            v___y_6382_,
                        );
                        if lean_obj_tag(v___x_6406_) == 0 {
                            v_a_6407_ = lean_ctor_get(v___x_6406_, 0);
                            lean_inc(v_a_6407_);
                            lean_dec_ref_known(v___x_6406_, 1);
                            v_b_6408_ = lean_array_fget_borrowed(v_bs_6375_, v_i_6376_);
                            v___x_6409_ = lean_box((v___x_6403_) as usize);
                            lean_inc_ref(v_compFieldVars_6373_);
                            lean_inc_ref(v_constMotive_6372_);
                            lean_inc(v_a_6405_);
                            lean_inc(v_b_6408_);
                            v___f_6410_ = lean_alloc_closure(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed as *mut core::ffi::c_void, 13, 5);
                            lean_closure_set(v___f_6410_, 0, v_b_6408_);
                            lean_closure_set(v___f_6410_, 1, v_a_6405_);
                            lean_closure_set(v___f_6410_, 2, v_constMotive_6372_);
                            lean_closure_set(v___f_6410_, 3, v___x_6409_);
                            lean_closure_set(v___f_6410_, 4, v_compFieldVars_6373_);
                            v___x_6411_ = 0;
                            v___x_6412_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_6407_, v___f_6410_, v___x_6411_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
                            v___y_6385_ = v___x_6412_;
                            state = 1;
                            continue;
                        } else {
                            v___y_6385_ = v___x_6406_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_6385_) == 0 {
                    v_a_6386_ = lean_ctor_get(v___y_6385_, 0);
                    lean_inc(v_a_6386_);
                    lean_dec_ref_known(v___y_6385_, 1);
                    v___x_6387_ = lean_unsigned_to_nat(1);
                    v___x_6388_ = lean_nat_add(v_i_6376_, v___x_6387_);
                    lean_dec(v_i_6376_);
                    v___x_6389_ = lean_array_push(v_cs_6377_, v_a_6386_);
                    v_i_6376_ = v___x_6388_;
                    v_cs_6377_ = v___x_6389_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_cs_6377_);
                    lean_dec(v_i_6376_);
                    lean_dec_ref(v_compFieldVars_6373_);
                    lean_dec_ref(v_constMotive_6372_);
                    v_a_6391_ = lean_ctor_get(v___y_6385_, 0);
                    v_isSharedCheck_6398_ = (!lean_is_exclusive(v___y_6385_)) as u8;
                    if v_isSharedCheck_6398_ == 0 {
                        v___x_6393_ = v___y_6385_;
                        v_isShared_6394_ = v_isSharedCheck_6398_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6391_);
                        lean_dec(v___y_6385_);
                        v___x_6393_ = lean_box(0);
                        v_isShared_6394_ = v_isSharedCheck_6398_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6394_ == 0 {
                    v___x_6396_ = v___x_6393_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_a_6391_);
                    v___x_6396_ = v_reuseFailAlloc_6397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(
    mut v_constMotive_6413_: *mut LeanObject,
    mut v_compFieldVars_6414_: *mut LeanObject,
    mut v_as_6415_: *mut LeanObject,
    mut v_bs_6416_: *mut LeanObject,
    mut v_i_6417_: *mut LeanObject,
    mut v_cs_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6425_: *mut LeanObject = core::ptr::null_mut();
    v_res_6425_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(
        v_constMotive_6413_,
        v_compFieldVars_6414_,
        v_as_6415_,
        v_bs_6416_,
        v_i_6417_,
        v_cs_6418_,
        v___y_6419_,
        v___y_6420_,
        v___y_6421_,
        v___y_6422_,
        v___y_6423_,
    );
    lean_dec(v___y_6423_);
    lean_dec_ref(v___y_6422_);
    lean_dec(v___y_6421_);
    lean_dec_ref(v___y_6420_);
    lean_dec_ref(v___y_6419_);
    lean_dec_ref(v_bs_6416_);
    lean_dec_ref(v_as_6415_);
    return v_res_6425_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(
    mut v_numIndices_6429_: *mut LeanObject,
    mut v___x_6430_: *mut LeanObject,
    mut v___x_6431_: *mut LeanObject,
    mut v_lparams_6432_: *mut LeanObject,
    mut v_params_6433_: *mut LeanObject,
    mut v_ctors_6434_: *mut LeanObject,
    mut v_compFieldVars_6435_: *mut LeanObject,
    mut v_levelParams_6436_: *mut LeanObject,
    mut v_xs_6437_: *mut LeanObject,
    mut v_constMotive_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
    mut v___y_6440_: *mut LeanObject,
    mut v___y_6441_: *mut LeanObject,
    mut v___y_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: u8 = 0;
    let mut v___x_6484_: u8 = 0;
    let mut v___x_6485_: u8 = 0;
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6490_: u8 = 0;
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6494_: u8 = 0;
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: u8 = 0;
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6445_ = lean_unsigned_to_nat(1);
                v___x_6446_ = lean_nat_add(v_numIndices_6429_, v___x_6445_);
                lean_inc(v___x_6446_);
                lean_inc_ref(v_xs_6437_);
                v___x_6447_ = l_Array_toSubarray___redArg(v_xs_6437_, v___x_6445_, v___x_6446_);
                v___x_6448_ = lean_unsigned_to_nat(0);
                v___x_6449_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2;
                v___x_6450_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_6447_, v___x_6449_);
                lean_inc_ref(v___x_6450_);
                lean_inc_ref(v_constMotive_6438_);
                v___f_6451_ = lean_alloc_closure(
                    l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed
                        as *mut core::ffi::c_void,
                    10,
                    3,
                );
                lean_closure_set(v___f_6451_, 0, v_constMotive_6438_);
                lean_closure_set(v___f_6451_, 1, v___x_6445_);
                lean_closure_set(v___f_6451_, 2, v___x_6450_);
                v___x_6452_ = lean_array_get_borrowed(v___x_6430_, v_xs_6437_, v___x_6446_);
                lean_dec(v___x_6446_);
                v___x_6495_ = lean_unsigned_to_nat(2);
                v___x_6496_ = lean_nat_add(v_numIndices_6429_, v___x_6495_);
                v___x_6497_ = lean_array_get_size(v_xs_6437_);
                v___x_6498_ = lean_nat_dec_le(v___x_6496_, v___x_6448_);
                if v___x_6498_ == 0 {
                    v___x_6499_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6499_, 0, v___x_6496_);
                    lean_ctor_set(v___x_6499_, 1, v___x_6497_);
                    v___y_6454_ = v___x_6499_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_6496_);
                    v___x_6500_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6500_, 0, v___x_6448_);
                    lean_ctor_set(v___x_6500_, 1, v___x_6497_);
                    v___y_6454_ = v___x_6500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v___x_6431_);
                v___x_6455_ = l_Lean_mkConst(v___x_6431_, v_lparams_6432_);
                lean_inc_ref(v_params_6433_);
                v___x_6456_ = l_Array_append___redArg(v_params_6433_, v___x_6450_);
                v___x_6457_ = l_Lean_mkAppN(v___x_6455_, v___x_6456_);
                lean_dec_ref(v___x_6456_);
                v___x_6458_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1;
                lean_inc_ref(v___x_6457_);
                v___x_6459_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_6458_, v___x_6457_, v___f_6451_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_);
                if lean_obj_tag(v___x_6459_) == 0 {
                    v_a_6460_ = lean_ctor_get(v___x_6459_, 0);
                    lean_inc(v_a_6460_);
                    lean_dec_ref_known(v___x_6459_, 1);
                    lean_inc(v___x_6452_);
                    v___x_6461_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
                        v___x_6457_,
                        v___x_6452_,
                        v___y_6440_,
                        v___y_6441_,
                        v___y_6442_,
                        v___y_6443_,
                    );
                    if lean_obj_tag(v___x_6461_) == 0 {
                        v_a_6462_ = lean_ctor_get(v___x_6461_, 0);
                        lean_inc(v_a_6462_);
                        lean_dec_ref_known(v___x_6461_, 1);
                        v_lower_6463_ = lean_ctor_get(v___y_6454_, 0);
                        lean_inc(v_lower_6463_);
                        v_upper_6464_ = lean_ctor_get(v___y_6454_, 1);
                        lean_inc(v_upper_6464_);
                        lean_dec_ref(v___y_6454_);
                        lean_inc_ref(v_xs_6437_);
                        v___x_6465_ =
                            l_Array_toSubarray___redArg(v_xs_6437_, v_lower_6463_, v_upper_6464_);
                        v___x_6466_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_6465_, v___x_6449_);
                        v___x_6467_ = lean_array_mk(v_ctors_6434_);
                        v___x_6468_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_6438_, v_compFieldVars_6435_, v___x_6466_, v___x_6467_, v___x_6448_, v___x_6449_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_);
                        lean_dec_ref(v___x_6467_);
                        lean_dec_ref(v___x_6466_);
                        if lean_obj_tag(v___x_6468_) == 0 {
                            v_a_6469_ = lean_ctor_get(v___x_6468_, 0);
                            lean_inc(v_a_6469_);
                            lean_dec_ref_known(v___x_6468_, 1);
                            lean_inc_ref(v_params_6433_);
                            v___x_6470_ = l_Array_append___redArg(v_params_6433_, v_xs_6437_);
                            lean_dec_ref(v_xs_6437_);
                            v___x_6471_ = l_Lean_mkCasesOnName(v___x_6431_);
                            v___x_6472_ = lean_box(0);
                            v___x_6473_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_6436_, v___x_6472_);
                            v___x_6474_ = l_Lean_mkConst(v___x_6471_, v___x_6473_);
                            v___x_6475_ = lean_mk_empty_array_with_capacity(v___x_6445_);
                            lean_inc_ref(v___x_6475_);
                            v___x_6476_ = lean_array_push(v___x_6475_, v_a_6460_);
                            v___x_6477_ = l_Array_append___redArg(v_params_6433_, v___x_6476_);
                            lean_dec_ref(v___x_6476_);
                            v___x_6478_ = l_Array_append___redArg(v___x_6477_, v___x_6450_);
                            lean_dec_ref(v___x_6450_);
                            v___x_6479_ = lean_array_push(v___x_6475_, v_a_6462_);
                            v___x_6480_ = l_Array_append___redArg(v___x_6478_, v___x_6479_);
                            lean_dec_ref(v___x_6479_);
                            v___x_6481_ = l_Array_append___redArg(v___x_6480_, v_a_6469_);
                            lean_dec(v_a_6469_);
                            v___x_6482_ = l_Lean_mkAppN(v___x_6474_, v___x_6481_);
                            lean_dec_ref(v___x_6481_);
                            v___x_6483_ = 0;
                            v___x_6484_ = 1;
                            v___x_6485_ = 1;
                            v___x_6486_ = l_Lean_Meta_mkLambdaFVars(
                                v___x_6470_,
                                v___x_6482_,
                                v___x_6483_,
                                v___x_6484_,
                                v___x_6483_,
                                v___x_6484_,
                                v___x_6485_,
                                v___y_6440_,
                                v___y_6441_,
                                v___y_6442_,
                                v___y_6443_,
                            );
                            lean_dec_ref(v___x_6470_);
                            return v___x_6486_;
                        } else {
                            lean_dec(v_a_6462_);
                            lean_dec(v_a_6460_);
                            lean_dec_ref(v___x_6450_);
                            lean_dec_ref(v_xs_6437_);
                            lean_dec(v_levelParams_6436_);
                            lean_dec_ref(v_params_6433_);
                            lean_dec(v___x_6431_);
                            v_a_6487_ = lean_ctor_get(v___x_6468_, 0);
                            v_isSharedCheck_6494_ = (!lean_is_exclusive(v___x_6468_)) as u8;
                            if v_isSharedCheck_6494_ == 0 {
                                v___x_6489_ = v___x_6468_;
                                v_isShared_6490_ = v_isSharedCheck_6494_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_6487_);
                                lean_dec(v___x_6468_);
                                v___x_6489_ = lean_box(0);
                                v_isShared_6490_ = v_isSharedCheck_6494_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6460_);
                        lean_dec_ref(v___y_6454_);
                        lean_dec_ref(v___x_6450_);
                        lean_dec_ref(v_constMotive_6438_);
                        lean_dec_ref(v_xs_6437_);
                        lean_dec(v_levelParams_6436_);
                        lean_dec_ref(v_compFieldVars_6435_);
                        lean_dec(v_ctors_6434_);
                        lean_dec_ref(v_params_6433_);
                        lean_dec(v___x_6431_);
                        return v___x_6461_;
                    }
                } else {
                    lean_dec_ref(v___x_6457_);
                    lean_dec_ref(v___y_6454_);
                    lean_dec_ref(v___x_6450_);
                    lean_dec_ref(v_constMotive_6438_);
                    lean_dec_ref(v_xs_6437_);
                    lean_dec(v_levelParams_6436_);
                    lean_dec_ref(v_compFieldVars_6435_);
                    lean_dec(v_ctors_6434_);
                    lean_dec_ref(v_params_6433_);
                    lean_dec(v___x_6431_);
                    return v___x_6459_;
                }
            }
            2 => {
                if v_isShared_6490_ == 0 {
                    v___x_6492_ = v___x_6489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6493_, 0, v_a_6487_);
                    v___x_6492_ = v_reuseFailAlloc_6493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(
    mut v_numIndices_6501_: *mut LeanObject,
    mut v___x_6502_: *mut LeanObject,
    mut v___x_6503_: *mut LeanObject,
    mut v_lparams_6504_: *mut LeanObject,
    mut v_params_6505_: *mut LeanObject,
    mut v_ctors_6506_: *mut LeanObject,
    mut v_compFieldVars_6507_: *mut LeanObject,
    mut v_levelParams_6508_: *mut LeanObject,
    mut v_xs_6509_: *mut LeanObject,
    mut v_constMotive_6510_: *mut LeanObject,
    mut v___y_6511_: *mut LeanObject,
    mut v___y_6512_: *mut LeanObject,
    mut v___y_6513_: *mut LeanObject,
    mut v___y_6514_: *mut LeanObject,
    mut v___y_6515_: *mut LeanObject,
    mut v___y_6516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6517_: *mut LeanObject = core::ptr::null_mut();
    v_res_6517_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(
        v_numIndices_6501_,
        v___x_6502_,
        v___x_6503_,
        v_lparams_6504_,
        v_params_6505_,
        v_ctors_6506_,
        v_compFieldVars_6507_,
        v_levelParams_6508_,
        v_xs_6509_,
        v_constMotive_6510_,
        v___y_6511_,
        v___y_6512_,
        v___y_6513_,
        v___y_6514_,
        v___y_6515_,
    );
    lean_dec(v___y_6515_);
    lean_dec_ref(v___y_6514_);
    lean_dec(v___y_6513_);
    lean_dec_ref(v___y_6512_);
    lean_dec_ref(v___y_6511_);
    lean_dec_ref(v___x_6502_);
    lean_dec(v_numIndices_6501_);
    return v_res_6517_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    v___x_6518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6518_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
    v___x_6520_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6520_, 0, v___x_6519_);
    return v___x_6520_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    v___x_6521_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
    v___x_6522_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6522_, 0, v___x_6521_);
    lean_ctor_set(v___x_6522_, 1, v___x_6521_);
    return v___x_6522_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    v___x_6523_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
    v___x_6524_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_6524_, 0, v___x_6523_);
    lean_ctor_set(v___x_6524_, 1, v___x_6523_);
    lean_ctor_set(v___x_6524_, 2, v___x_6523_);
    lean_ctor_set(v___x_6524_, 3, v___x_6523_);
    lean_ctor_set(v___x_6524_, 4, v___x_6523_);
    lean_ctor_set(v___x_6524_, 5, v___x_6523_);
    return v___x_6524_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(
    mut v_env_6525_: *mut LeanObject,
    mut v___y_6526_: *mut LeanObject,
    mut v___y_6527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6539_: u8 = 0;
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6551_: u8 = 0;
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6559_: u8 = 0;
    let mut v_unused_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6562_: u8 = 0;
    let mut v_unused_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6529_ = lean_st_ref_take(v___y_6527_);
                v_nextMacroScope_6530_ = lean_ctor_get(v___x_6529_, 1);
                v_ngen_6531_ = lean_ctor_get(v___x_6529_, 2);
                v_auxDeclNGen_6532_ = lean_ctor_get(v___x_6529_, 3);
                v_traceState_6533_ = lean_ctor_get(v___x_6529_, 4);
                v_messages_6534_ = lean_ctor_get(v___x_6529_, 6);
                v_infoState_6535_ = lean_ctor_get(v___x_6529_, 7);
                v_snapshotTasks_6536_ = lean_ctor_get(v___x_6529_, 8);
                v_isSharedCheck_6562_ = (!lean_is_exclusive(v___x_6529_)) as u8;
                if v_isSharedCheck_6562_ == 0 {
                    v_unused_6563_ = lean_ctor_get(v___x_6529_, 5);
                    lean_dec(v_unused_6563_);
                    v_unused_6564_ = lean_ctor_get(v___x_6529_, 0);
                    lean_dec(v_unused_6564_);
                    v___x_6538_ = v___x_6529_;
                    v_isShared_6539_ = v_isSharedCheck_6562_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6536_);
                    lean_inc(v_infoState_6535_);
                    lean_inc(v_messages_6534_);
                    lean_inc(v_traceState_6533_);
                    lean_inc(v_auxDeclNGen_6532_);
                    lean_inc(v_ngen_6531_);
                    lean_inc(v_nextMacroScope_6530_);
                    lean_dec(v___x_6529_);
                    v___x_6538_ = lean_box(0);
                    v_isShared_6539_ = v_isSharedCheck_6562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6540_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
                if v_isShared_6539_ == 0 {
                    lean_ctor_set(v___x_6538_, 5, v___x_6540_);
                    lean_ctor_set(v___x_6538_, 0, v_env_6525_);
                    v___x_6542_ = v___x_6538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6561_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_env_6525_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 1, v_nextMacroScope_6530_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 2, v_ngen_6531_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 3, v_auxDeclNGen_6532_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 4, v_traceState_6533_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 5, v___x_6540_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 6, v_messages_6534_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 7, v_infoState_6535_);
                    lean_ctor_set(v_reuseFailAlloc_6561_, 8, v_snapshotTasks_6536_);
                    v___x_6542_ = v_reuseFailAlloc_6561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6543_ = lean_st_ref_set(v___y_6527_, v___x_6542_);
                v___x_6544_ = lean_st_ref_take(v___y_6526_);
                v_mctx_6545_ = lean_ctor_get(v___x_6544_, 0);
                v_zetaDeltaFVarIds_6546_ = lean_ctor_get(v___x_6544_, 2);
                v_postponed_6547_ = lean_ctor_get(v___x_6544_, 3);
                v_diag_6548_ = lean_ctor_get(v___x_6544_, 4);
                v_isSharedCheck_6559_ = (!lean_is_exclusive(v___x_6544_)) as u8;
                if v_isSharedCheck_6559_ == 0 {
                    v_unused_6560_ = lean_ctor_get(v___x_6544_, 1);
                    lean_dec(v_unused_6560_);
                    v___x_6550_ = v___x_6544_;
                    v_isShared_6551_ = v_isSharedCheck_6559_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_6548_);
                    lean_inc(v_postponed_6547_);
                    lean_inc(v_zetaDeltaFVarIds_6546_);
                    lean_inc(v_mctx_6545_);
                    lean_dec(v___x_6544_);
                    v___x_6550_ = lean_box(0);
                    v_isShared_6551_ = v_isSharedCheck_6559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6552_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
                if v_isShared_6551_ == 0 {
                    lean_ctor_set(v___x_6550_, 1, v___x_6552_);
                    v___x_6554_ = v___x_6550_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6558_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_mctx_6545_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 1, v___x_6552_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 2, v_zetaDeltaFVarIds_6546_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 3, v_postponed_6547_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 4, v_diag_6548_);
                    v___x_6554_ = v_reuseFailAlloc_6558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6555_ = lean_st_ref_set(v___y_6526_, v___x_6554_);
                v___x_6556_ = lean_box(0);
                v___x_6557_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6557_, 0, v___x_6556_);
                return v___x_6557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(
    mut v_env_6565_: *mut LeanObject,
    mut v___y_6566_: *mut LeanObject,
    mut v___y_6567_: *mut LeanObject,
    mut v___y_6568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6569_: *mut LeanObject = core::ptr::null_mut();
    v_res_6569_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_6565_, v___y_6566_, v___y_6567_);
    lean_dec(v___y_6567_);
    lean_dec(v___y_6566_);
    return v_res_6569_;
}
pub unsafe fn l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(
    mut v_declName_6570_: *mut LeanObject,
    mut v_impName_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6584_: u8 = 0;
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6590_: u8 = 0;
    let mut v_a_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6578_ = lean_st_ref_get(v___y_6576_);
                v_env_6579_ = lean_ctor_get(v___x_6578_, 0);
                lean_inc_ref(v_env_6579_);
                lean_dec(v___x_6578_);
                v___x_6580_ = l_Lean_Compiler_setImplementedBy(
                    v_env_6579_,
                    v_declName_6570_,
                    v_impName_6571_,
                );
                if lean_obj_tag(v___x_6580_) == 0 {
                    v_a_6581_ = lean_ctor_get(v___x_6580_, 0);
                    v_isSharedCheck_6590_ = (!lean_is_exclusive(v___x_6580_)) as u8;
                    if v_isSharedCheck_6590_ == 0 {
                        v___x_6583_ = v___x_6580_;
                        v_isShared_6584_ = v_isSharedCheck_6590_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6581_);
                        lean_dec(v___x_6580_);
                        v___x_6583_ = lean_box(0);
                        v_isShared_6584_ = v_isSharedCheck_6590_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6591_ = lean_ctor_get(v___x_6580_, 0);
                    lean_inc(v_a_6591_);
                    lean_dec_ref_known(v___x_6580_, 1);
                    v___x_6592_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_6591_, v___y_6574_, v___y_6576_);
                    return v___x_6592_;
                }
            }
            1 => {
                if v_isShared_6584_ == 0 {
                    lean_ctor_set_tag(v___x_6583_, 3);
                    v___x_6586_ = v___x_6583_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6589_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6589_, 0, v_a_6581_);
                    v___x_6586_ = v_reuseFailAlloc_6589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6587_ = l_Lean_MessageData_ofFormat(v___x_6586_);
                v___x_6588_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_6587_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
                return v___x_6588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(
    mut v_declName_6593_: *mut LeanObject,
    mut v_impName_6594_: *mut LeanObject,
    mut v___y_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
    mut v___y_6597_: *mut LeanObject,
    mut v___y_6598_: *mut LeanObject,
    mut v___y_6599_: *mut LeanObject,
    mut v___y_6600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6601_: *mut LeanObject = core::ptr::null_mut();
    v_res_6601_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(
        v_declName_6593_,
        v_impName_6594_,
        v___y_6595_,
        v___y_6596_,
        v___y_6597_,
        v___y_6598_,
        v___y_6599_,
    );
    lean_dec(v___y_6599_);
    lean_dec_ref(v___y_6598_);
    lean_dec(v___y_6597_);
    lean_dec_ref(v___y_6596_);
    lean_dec_ref(v___y_6595_);
    return v_res_6601_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(
    mut v_msg_6602_: *mut LeanObject,
    mut v___y_6603_: *mut LeanObject,
    mut v___y_6604_: *mut LeanObject,
    mut v___y_6605_: *mut LeanObject,
    mut v___y_6606_: *mut LeanObject,
    mut v___y_6607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6614_: u8 = 0;
    let mut v_toFunctor_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___f_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6638_: u8 = 0;
    let mut v_toFunctor_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6645_: u8 = 0;
    let mut v___f_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11231__overap_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6665_: u8 = 0;
    let mut v_unused_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6667_: u8 = 0;
    let mut v_unused_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6671_: u8 = 0;
    let mut v_unused_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6673_: u8 = 0;
    let mut v_unused_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6609_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
                v___x_6610_ = l_StateRefT_x27_instMonad___redArg(v___x_6609_);
                v_toApplicative_6611_ = lean_ctor_get(v___x_6610_, 0);
                v_isSharedCheck_6673_ = (!lean_is_exclusive(v___x_6610_)) as u8;
                if v_isSharedCheck_6673_ == 0 {
                    v_unused_6674_ = lean_ctor_get(v___x_6610_, 1);
                    lean_dec(v_unused_6674_);
                    v___x_6613_ = v___x_6610_;
                    v_isShared_6614_ = v_isSharedCheck_6673_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_6611_);
                    lean_dec(v___x_6610_);
                    v___x_6613_ = lean_box(0);
                    v_isShared_6614_ = v_isSharedCheck_6673_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6615_ = lean_ctor_get(v_toApplicative_6611_, 0);
                v_toSeq_6616_ = lean_ctor_get(v_toApplicative_6611_, 2);
                v_toSeqLeft_6617_ = lean_ctor_get(v_toApplicative_6611_, 3);
                v_toSeqRight_6618_ = lean_ctor_get(v_toApplicative_6611_, 4);
                v_isSharedCheck_6671_ = (!lean_is_exclusive(v_toApplicative_6611_)) as u8;
                if v_isSharedCheck_6671_ == 0 {
                    v_unused_6672_ = lean_ctor_get(v_toApplicative_6611_, 1);
                    lean_dec(v_unused_6672_);
                    v___x_6620_ = v_toApplicative_6611_;
                    v_isShared_6621_ = v_isSharedCheck_6671_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_6618_);
                    lean_inc(v_toSeqLeft_6617_);
                    lean_inc(v_toSeq_6616_);
                    lean_inc(v_toFunctor_6615_);
                    lean_dec(v_toApplicative_6611_);
                    v___x_6620_ = lean_box(0);
                    v_isShared_6621_ = v_isSharedCheck_6671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6622_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1;
                v___f_6623_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_6615_);
                v___f_6624_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6624_, 0, v_toFunctor_6615_);
                v___f_6625_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6625_, 0, v_toFunctor_6615_);
                v___x_6626_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6626_, 0, v___f_6624_);
                lean_ctor_set(v___x_6626_, 1, v___f_6625_);
                v___f_6627_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6627_, 0, v_toSeqRight_6618_);
                v___f_6628_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6628_, 0, v_toSeqLeft_6617_);
                v___f_6629_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6629_, 0, v_toSeq_6616_);
                if v_isShared_6621_ == 0 {
                    lean_ctor_set(v___x_6620_, 4, v___f_6627_);
                    lean_ctor_set(v___x_6620_, 3, v___f_6628_);
                    lean_ctor_set(v___x_6620_, 2, v___f_6629_);
                    lean_ctor_set(v___x_6620_, 1, v___f_6622_);
                    lean_ctor_set(v___x_6620_, 0, v___x_6626_);
                    v___x_6631_ = v___x_6620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 0, v___x_6626_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 1, v___f_6622_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 2, v___f_6629_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 3, v___f_6628_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 4, v___f_6627_);
                    v___x_6631_ = v_reuseFailAlloc_6670_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6614_ == 0 {
                    lean_ctor_set(v___x_6613_, 1, v___f_6623_);
                    lean_ctor_set(v___x_6613_, 0, v___x_6631_);
                    v___x_6633_ = v___x_6613_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6669_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6669_, 0, v___x_6631_);
                    lean_ctor_set(v_reuseFailAlloc_6669_, 1, v___f_6623_);
                    v___x_6633_ = v_reuseFailAlloc_6669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6634_ = l_StateRefT_x27_instMonad___redArg(v___x_6633_);
                v_toApplicative_6635_ = lean_ctor_get(v___x_6634_, 0);
                v_isSharedCheck_6667_ = (!lean_is_exclusive(v___x_6634_)) as u8;
                if v_isSharedCheck_6667_ == 0 {
                    v_unused_6668_ = lean_ctor_get(v___x_6634_, 1);
                    lean_dec(v_unused_6668_);
                    v___x_6637_ = v___x_6634_;
                    v_isShared_6638_ = v_isSharedCheck_6667_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_6635_);
                    lean_dec(v___x_6634_);
                    v___x_6637_ = lean_box(0);
                    v_isShared_6638_ = v_isSharedCheck_6667_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_6639_ = lean_ctor_get(v_toApplicative_6635_, 0);
                v_toSeq_6640_ = lean_ctor_get(v_toApplicative_6635_, 2);
                v_toSeqLeft_6641_ = lean_ctor_get(v_toApplicative_6635_, 3);
                v_toSeqRight_6642_ = lean_ctor_get(v_toApplicative_6635_, 4);
                v_isSharedCheck_6665_ = (!lean_is_exclusive(v_toApplicative_6635_)) as u8;
                if v_isSharedCheck_6665_ == 0 {
                    v_unused_6666_ = lean_ctor_get(v_toApplicative_6635_, 1);
                    lean_dec(v_unused_6666_);
                    v___x_6644_ = v_toApplicative_6635_;
                    v_isShared_6645_ = v_isSharedCheck_6665_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_6642_);
                    lean_inc(v_toSeqLeft_6641_);
                    lean_inc(v_toSeq_6640_);
                    lean_inc(v_toFunctor_6639_);
                    lean_dec(v_toApplicative_6635_);
                    v___x_6644_ = lean_box(0);
                    v_isShared_6645_ = v_isSharedCheck_6665_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_6646_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0;
                v___f_6647_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1;
                lean_inc_ref(v_toFunctor_6639_);
                v___f_6648_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6648_, 0, v_toFunctor_6639_);
                v___f_6649_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6649_, 0, v_toFunctor_6639_);
                v___x_6650_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6650_, 0, v___f_6648_);
                lean_ctor_set(v___x_6650_, 1, v___f_6649_);
                v___f_6651_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6651_, 0, v_toSeqRight_6642_);
                v___f_6652_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6652_, 0, v_toSeqLeft_6641_);
                v___f_6653_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_6653_, 0, v_toSeq_6640_);
                if v_isShared_6645_ == 0 {
                    lean_ctor_set(v___x_6644_, 4, v___f_6651_);
                    lean_ctor_set(v___x_6644_, 3, v___f_6652_);
                    lean_ctor_set(v___x_6644_, 2, v___f_6653_);
                    lean_ctor_set(v___x_6644_, 1, v___f_6646_);
                    lean_ctor_set(v___x_6644_, 0, v___x_6650_);
                    v___x_6655_ = v___x_6644_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 0, v___x_6650_);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 1, v___f_6646_);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 2, v___f_6653_);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 3, v___f_6652_);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 4, v___f_6651_);
                    v___x_6655_ = v_reuseFailAlloc_6664_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6638_ == 0 {
                    lean_ctor_set(v___x_6637_, 1, v___f_6647_);
                    lean_ctor_set(v___x_6637_, 0, v___x_6655_);
                    v___x_6657_ = v___x_6637_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6663_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6663_, 0, v___x_6655_);
                    lean_ctor_set(v_reuseFailAlloc_6663_, 1, v___f_6647_);
                    v___x_6657_ = v_reuseFailAlloc_6663_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6658_ = l_ReaderT_instMonad___redArg(v___x_6657_);
                v___x_6659_ = lean_box(0);
                v___x_6660_ = l_instInhabitedOfMonad___redArg(v___x_6658_, v___x_6659_);
                v___x_11231__overap_6661_ = lean_panic_fn_borrowed(v___x_6660_, v_msg_6602_);
                lean_dec(v___x_6660_);
                lean_inc(v___y_6607_);
                lean_inc_ref(v___y_6606_);
                lean_inc(v___y_6605_);
                lean_inc_ref(v___y_6604_);
                lean_inc_ref(v___y_6603_);
                v___x_6662_ = lean_apply_6(
                    v___x_11231__overap_6661_,
                    v___y_6603_,
                    v___y_6604_,
                    v___y_6605_,
                    v___y_6606_,
                    v___y_6607_,
                    lean_box(0),
                );
                return v___x_6662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(
    mut v_msg_6675_: *mut LeanObject,
    mut v___y_6676_: *mut LeanObject,
    mut v___y_6677_: *mut LeanObject,
    mut v___y_6678_: *mut LeanObject,
    mut v___y_6679_: *mut LeanObject,
    mut v___y_6680_: *mut LeanObject,
    mut v___y_6681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6682_: *mut LeanObject = core::ptr::null_mut();
    v_res_6682_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_6675_, v___y_6676_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
    lean_dec(v___y_6680_);
    lean_dec_ref(v___y_6679_);
    lean_dec(v___y_6678_);
    lean_dec_ref(v___y_6677_);
    lean_dec_ref(v___y_6676_);
    return v_res_6682_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    v___x_6684_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0;
    v___x_6685_ = l_Lean_stringToMessageData(v___x_6684_);
    return v___x_6685_;
}
pub unsafe fn _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    v___x_6687_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6;
    v___x_6688_ = lean_unsigned_to_nat(11);
    v___x_6689_ = lean_unsigned_to_nat(115);
    v___x_6690_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2;
    v___x_6691_ =
        l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4;
    v___x_6692_ = l_mkPanicMessageWithDecl(
        v___x_6691_,
        v___x_6690_,
        v___x_6689_,
        v___x_6688_,
        v___x_6687_,
    );
    return v___x_6692_;
}
pub unsafe fn l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(
    mut v_constName_6693_: *mut LeanObject,
    mut v___y_6694_: *mut LeanObject,
    mut v___y_6695_: *mut LeanObject,
    mut v___y_6696_: *mut LeanObject,
    mut v___y_6697_: *mut LeanObject,
    mut v___y_6698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: u8 = 0;
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: u8 = 0;
    let mut v___x_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6713_: u8 = 0;
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6728_: u8 = 0;
    let mut v_val_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6733_: u8 = 0;
    let mut v_a_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6737_: u8 = 0;
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6708_ = lean_st_ref_get(v___y_6698_);
                v_env_6709_ = lean_ctor_get(v___x_6708_, 0);
                lean_inc_ref(v_env_6709_);
                lean_dec(v___x_6708_);
                v___x_6710_ = 0;
                lean_inc(v_constName_6693_);
                v___x_6711_ =
                    l_Lean_Environment_findAsync_x3f(v_env_6709_, v_constName_6693_, v___x_6710_);
                if lean_obj_tag(v___x_6711_) == 1 {
                    v_val_6712_ = lean_ctor_get(v___x_6711_, 0);
                    lean_inc(v_val_6712_);
                    lean_dec_ref_known(v___x_6711_, 1);
                    v_kind_6713_ = lean_ctor_get_uint8(
                        v_val_6712_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_kind_6713_ == 0 {
                        v___x_6714_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_6712_);
                        if lean_obj_tag(v___x_6714_) == 1 {
                            lean_dec(v_constName_6693_);
                            v_val_6715_ = lean_ctor_get(v___x_6714_, 0);
                            v_isSharedCheck_6722_ = (!lean_is_exclusive(v___x_6714_)) as u8;
                            if v_isSharedCheck_6722_ == 0 {
                                v___x_6717_ = v___x_6714_;
                                v_isShared_6718_ = v_isSharedCheck_6722_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_6715_);
                                lean_dec(v___x_6714_);
                                v___x_6717_ = lean_box(0);
                                v_isShared_6718_ = v_isSharedCheck_6722_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_6714_);
                            v___x_6723_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once), _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
                            v___x_6724_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_6723_, v___y_6694_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_);
                            if lean_obj_tag(v___x_6724_) == 0 {
                                v_a_6725_ = lean_ctor_get(v___x_6724_, 0);
                                v_isSharedCheck_6733_ = (!lean_is_exclusive(v___x_6724_)) as u8;
                                if v_isSharedCheck_6733_ == 0 {
                                    v___x_6727_ = v___x_6724_;
                                    v_isShared_6728_ = v_isSharedCheck_6733_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_6725_);
                                    lean_dec(v___x_6724_);
                                    v___x_6727_ = lean_box(0);
                                    v_isShared_6728_ = v_isSharedCheck_6733_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_constName_6693_);
                                v_a_6734_ = lean_ctor_get(v___x_6724_, 0);
                                v_isSharedCheck_6741_ = (!lean_is_exclusive(v___x_6724_)) as u8;
                                if v_isSharedCheck_6741_ == 0 {
                                    v___x_6736_ = v___x_6724_;
                                    v_isShared_6737_ = v_isSharedCheck_6741_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_6734_);
                                    lean_dec(v___x_6724_);
                                    v___x_6736_ = lean_box(0);
                                    v_isShared_6737_ = v_isSharedCheck_6741_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_val_6712_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6711_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6701_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
                v___x_6702_ = 0;
                v___x_6703_ = l_Lean_MessageData_ofConstName(v_constName_6693_, v___x_6702_);
                v___x_6704_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6704_, 0, v___x_6701_);
                lean_ctor_set(v___x_6704_, 1, v___x_6703_);
                v___x_6705_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once), _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
                v___x_6706_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6706_, 0, v___x_6704_);
                lean_ctor_set(v___x_6706_, 1, v___x_6705_);
                v___x_6707_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_6706_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_);
                return v___x_6707_;
            }
            2 => {
                if v_isShared_6718_ == 0 {
                    lean_ctor_set_tag(v___x_6717_, 0);
                    v___x_6720_ = v___x_6717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6721_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6721_, 0, v_val_6715_);
                    v___x_6720_ = v_reuseFailAlloc_6721_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6720_;
            }
            4 => {
                if lean_obj_tag(v_a_6725_) == 0 {
                    lean_del_object(v___x_6727_);
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_constName_6693_);
                    v_val_6729_ = lean_ctor_get(v_a_6725_, 0);
                    lean_inc(v_val_6729_);
                    lean_dec_ref_known(v_a_6725_, 1);
                    if v_isShared_6728_ == 0 {
                        lean_ctor_set(v___x_6727_, 0, v_val_6729_);
                        v___x_6731_ = v___x_6727_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6732_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6732_, 0, v_val_6729_);
                        v___x_6731_ = v_reuseFailAlloc_6732_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_6731_;
            }
            6 => {
                if v_isShared_6737_ == 0 {
                    v___x_6739_ = v___x_6736_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6740_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6740_, 0, v_a_6734_);
                    v___x_6739_ = v_reuseFailAlloc_6740_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(
    mut v_constName_6742_: *mut LeanObject,
    mut v___y_6743_: *mut LeanObject,
    mut v___y_6744_: *mut LeanObject,
    mut v___y_6745_: *mut LeanObject,
    mut v___y_6746_: *mut LeanObject,
    mut v___y_6747_: *mut LeanObject,
    mut v___y_6748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6749_: *mut LeanObject = core::ptr::null_mut();
    v_res_6749_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(
        v_constName_6742_,
        v___y_6743_,
        v___y_6744_,
        v___y_6745_,
        v___y_6746_,
        v___y_6747_,
    );
    lean_dec(v___y_6747_);
    lean_dec_ref(v___y_6746_);
    lean_dec(v___y_6745_);
    lean_dec_ref(v___y_6744_);
    lean_dec_ref(v___y_6743_);
    return v_res_6749_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn(
    mut v_a_6753_: *mut LeanObject,
    mut v_a_6754_: *mut LeanObject,
    mut v_a_6755_: *mut LeanObject,
    mut v_a_6756_: *mut LeanObject,
    mut v_a_6757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInductiveVal_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lparams_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_compFieldVars_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v_toConstantVal_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6779_: u8 = 0;
    let mut v_levelParams_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: u8 = 0;
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: u8 = 0;
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: u8 = 0;
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6814_: u8 = 0;
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6818_: u8 = 0;
    let mut v_a_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6826_: u8 = 0;
    let mut v_isSharedCheck_6827_: u8 = 0;
    let mut v_unused_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6829_: u8 = 0;
    let mut v_unused_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6833_: u8 = 0;
    let mut v_unused_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInductiveVal_6759_ = lean_ctor_get(v_a_6753_, 0);
                v_toConstantVal_6760_ = lean_ctor_get(v_toInductiveVal_6759_, 0);
                v_lparams_6761_ = lean_ctor_get(v_a_6753_, 1);
                v_params_6762_ = lean_ctor_get(v_a_6753_, 2);
                v_compFieldVars_6763_ = lean_ctor_get(v_a_6753_, 4);
                v_numIndices_6764_ = lean_ctor_get(v_toInductiveVal_6759_, 2);
                v_ctors_6765_ = lean_ctor_get(v_toInductiveVal_6759_, 4);
                v_name_6766_ = lean_ctor_get(v_toConstantVal_6760_, 0);
                lean_inc(v_name_6766_);
                v___x_6767_ = l_Lean_mkCasesOnName(v_name_6766_);
                lean_inc(v___x_6767_);
                v___x_6768_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_6767_, v_a_6753_, v_a_6754_, v_a_6755_, v_a_6756_, v_a_6757_);
                if lean_obj_tag(v___x_6768_) == 0 {
                    v_a_6769_ = lean_ctor_get(v___x_6768_, 0);
                    lean_inc(v_a_6769_);
                    lean_dec_ref_known(v___x_6768_, 1);
                    v___x_6770_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1;
                    lean_inc(v_name_6766_);
                    v___x_6771_ = l_Lean_Name_append(v_name_6766_, v___x_6770_);
                    lean_inc(v___x_6771_);
                    v___x_6772_ =
                        l_Lean_mkCasesOn(v___x_6771_, v_a_6754_, v_a_6755_, v_a_6756_, v_a_6757_);
                    if lean_obj_tag(v___x_6772_) == 0 {
                        v_isSharedCheck_6833_ = (!lean_is_exclusive(v___x_6772_)) as u8;
                        if v_isSharedCheck_6833_ == 0 {
                            v_unused_6834_ = lean_ctor_get(v___x_6772_, 0);
                            lean_dec(v_unused_6834_);
                            v___x_6774_ = v___x_6772_;
                            v_isShared_6775_ = v_isSharedCheck_6833_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6772_);
                            v___x_6774_ = lean_box(0);
                            v_isShared_6775_ = v_isSharedCheck_6833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6771_);
                        lean_dec(v_a_6769_);
                        lean_dec(v___x_6767_);
                        return v___x_6772_;
                    }
                } else {
                    lean_dec(v___x_6767_);
                    v_a_6835_ = lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6842_ = (!lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6842_ == 0 {
                        v___x_6837_ = v___x_6768_;
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6835_);
                        lean_dec(v___x_6768_);
                        v___x_6837_ = lean_box(0);
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_toConstantVal_6776_ = lean_ctor_get(v_a_6769_, 0);
                v_isSharedCheck_6829_ = (!lean_is_exclusive(v_a_6769_)) as u8;
                if v_isSharedCheck_6829_ == 0 {
                    v_unused_6830_ = lean_ctor_get(v_a_6769_, 3);
                    lean_dec(v_unused_6830_);
                    v_unused_6831_ = lean_ctor_get(v_a_6769_, 2);
                    lean_dec(v_unused_6831_);
                    v_unused_6832_ = lean_ctor_get(v_a_6769_, 1);
                    lean_dec(v_unused_6832_);
                    v___x_6778_ = v_a_6769_;
                    v_isShared_6779_ = v_isSharedCheck_6829_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toConstantVal_6776_);
                    lean_dec(v_a_6769_);
                    v___x_6778_ = lean_box(0);
                    v_isShared_6779_ = v_isSharedCheck_6829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_levelParams_6780_ = lean_ctor_get(v_toConstantVal_6776_, 1);
                v_type_6781_ = lean_ctor_get(v_toConstantVal_6776_, 2);
                v_isSharedCheck_6827_ = (!lean_is_exclusive(v_toConstantVal_6776_)) as u8;
                if v_isSharedCheck_6827_ == 0 {
                    v_unused_6828_ = lean_ctor_get(v_toConstantVal_6776_, 0);
                    lean_dec(v_unused_6828_);
                    v___x_6783_ = v_toConstantVal_6776_;
                    v_isShared_6784_ = v_isSharedCheck_6827_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_type_6781_);
                    lean_inc(v_levelParams_6780_);
                    lean_dec(v_toConstantVal_6776_);
                    v___x_6783_ = lean_box(0);
                    v_isShared_6784_ = v_isSharedCheck_6827_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_type_6781_);
                v___x_6785_ = l_Lean_Meta_instantiateForall(
                    v_type_6781_,
                    v_params_6762_,
                    v_a_6754_,
                    v_a_6755_,
                    v_a_6756_,
                    v_a_6757_,
                );
                if lean_obj_tag(v___x_6785_) == 0 {
                    v_a_6786_ = lean_ctor_get(v___x_6785_, 0);
                    lean_inc(v_a_6786_);
                    lean_dec_ref_known(v___x_6785_, 1);
                    v___x_6787_ = l_Lean_instInhabitedExpr;
                    lean_inc(v_levelParams_6780_);
                    lean_inc_ref(v_compFieldVars_6763_);
                    lean_inc(v_ctors_6765_);
                    lean_inc_ref(v_params_6762_);
                    lean_inc(v_lparams_6761_);
                    lean_inc(v_numIndices_6764_);
                    v___f_6788_ = lean_alloc_closure(
                        l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed
                            as *mut core::ffi::c_void,
                        16,
                        8,
                    );
                    lean_closure_set(v___f_6788_, 0, v_numIndices_6764_);
                    lean_closure_set(v___f_6788_, 1, v___x_6787_);
                    lean_closure_set(v___f_6788_, 2, v___x_6771_);
                    lean_closure_set(v___f_6788_, 3, v_lparams_6761_);
                    lean_closure_set(v___f_6788_, 4, v_params_6762_);
                    lean_closure_set(v___f_6788_, 5, v_ctors_6765_);
                    lean_closure_set(v___f_6788_, 6, v_compFieldVars_6763_);
                    lean_closure_set(v___f_6788_, 7, v_levelParams_6780_);
                    v___x_6789_ = 0;
                    v___x_6790_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_6786_, v___f_6788_, v___x_6789_, v_a_6753_, v_a_6754_, v_a_6755_, v_a_6756_, v_a_6757_);
                    if lean_obj_tag(v___x_6790_) == 0 {
                        v_a_6791_ = lean_ctor_get(v___x_6790_, 0);
                        lean_inc(v_a_6791_);
                        lean_dec_ref_known(v___x_6790_, 1);
                        v___x_6792_ = l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                        lean_inc(v___x_6767_);
                        v___x_6793_ = l_Lean_Name_append(v___x_6767_, v___x_6792_);
                        lean_inc(v___x_6793_);
                        if v_isShared_6784_ == 0 {
                            lean_ctor_set(v___x_6783_, 0, v___x_6793_);
                            v___x_6795_ = v___x_6783_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6810_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6810_, 0, v___x_6793_);
                            lean_ctor_set(v_reuseFailAlloc_6810_, 1, v_levelParams_6780_);
                            lean_ctor_set(v_reuseFailAlloc_6810_, 2, v_type_6781_);
                            v___x_6795_ = v_reuseFailAlloc_6810_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_6783_);
                        lean_dec_ref(v_type_6781_);
                        lean_dec(v_levelParams_6780_);
                        lean_del_object(v___x_6778_);
                        lean_del_object(v___x_6774_);
                        lean_dec(v___x_6767_);
                        v_a_6811_ = lean_ctor_get(v___x_6790_, 0);
                        v_isSharedCheck_6818_ = (!lean_is_exclusive(v___x_6790_)) as u8;
                        if v_isSharedCheck_6818_ == 0 {
                            v___x_6813_ = v___x_6790_;
                            v_isShared_6814_ = v_isSharedCheck_6818_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6811_);
                            lean_dec(v___x_6790_);
                            v___x_6813_ = lean_box(0);
                            v_isShared_6814_ = v_isSharedCheck_6818_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6783_);
                    lean_dec_ref(v_type_6781_);
                    lean_dec(v_levelParams_6780_);
                    lean_del_object(v___x_6778_);
                    lean_del_object(v___x_6774_);
                    lean_dec(v___x_6771_);
                    lean_dec(v___x_6767_);
                    v_a_6819_ = lean_ctor_get(v___x_6785_, 0);
                    v_isSharedCheck_6826_ = (!lean_is_exclusive(v___x_6785_)) as u8;
                    if v_isSharedCheck_6826_ == 0 {
                        v___x_6821_ = v___x_6785_;
                        v_isShared_6822_ = v_isSharedCheck_6826_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6819_);
                        lean_dec(v___x_6785_);
                        v___x_6821_ = lean_box(0);
                        v_isShared_6822_ = v_isSharedCheck_6826_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6796_ = lean_box(0);
                v___x_6797_ = 0;
                v___x_6798_ = lean_box(0);
                lean_inc(v___x_6793_);
                v___x_6799_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6799_, 0, v___x_6793_);
                lean_ctor_set(v___x_6799_, 1, v___x_6798_);
                if v_isShared_6779_ == 0 {
                    lean_ctor_set(v___x_6778_, 3, v___x_6799_);
                    lean_ctor_set(v___x_6778_, 2, v___x_6796_);
                    lean_ctor_set(v___x_6778_, 1, v_a_6791_);
                    lean_ctor_set(v___x_6778_, 0, v___x_6795_);
                    v___x_6801_ = v___x_6778_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6809_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 0, v___x_6795_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 1, v_a_6791_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 2, v___x_6796_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 3, v___x_6799_);
                    v___x_6801_ = v_reuseFailAlloc_6809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_6801_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_6797_,
                );
                if v_isShared_6775_ == 0 {
                    lean_ctor_set_tag(v___x_6774_, 1);
                    lean_ctor_set(v___x_6774_, 0, v___x_6801_);
                    v___x_6803_ = v___x_6774_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6808_, 0, v___x_6801_);
                    v___x_6803_ = v_reuseFailAlloc_6808_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6804_ = l_Lean_addDecl(v___x_6803_, v___x_6789_, v_a_6756_, v_a_6757_);
                if lean_obj_tag(v___x_6804_) == 0 {
                    lean_dec_ref_known(v___x_6804_, 1);
                    v___x_6805_ = 0;
                    lean_inc(v___x_6793_);
                    v___x_6806_ = l_Lean_Meta_setInlineAttribute(
                        v___x_6793_,
                        v___x_6805_,
                        v_a_6754_,
                        v_a_6755_,
                        v_a_6756_,
                        v_a_6757_,
                    );
                    if lean_obj_tag(v___x_6806_) == 0 {
                        lean_dec_ref_known(v___x_6806_, 1);
                        v___x_6807_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_6767_, v___x_6793_, v_a_6753_, v_a_6754_, v_a_6755_, v_a_6756_, v_a_6757_);
                        return v___x_6807_;
                    } else {
                        lean_dec(v___x_6793_);
                        lean_dec(v___x_6767_);
                        return v___x_6806_;
                    }
                } else {
                    lean_dec(v___x_6793_);
                    lean_dec(v___x_6767_);
                    return v___x_6804_;
                }
            }
            7 => {
                if v_isShared_6814_ == 0 {
                    v___x_6816_ = v___x_6813_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6817_, 0, v_a_6811_);
                    v___x_6816_ = v_reuseFailAlloc_6817_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6816_;
            }
            9 => {
                if v_isShared_6822_ == 0 {
                    v___x_6824_ = v___x_6821_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6825_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6825_, 0, v_a_6819_);
                    v___x_6824_ = v_reuseFailAlloc_6825_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6824_;
            }
            11 => {
                if v_isShared_6838_ == 0 {
                    v___x_6840_ = v___x_6837_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6841_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
                    v___x_6840_ = v_reuseFailAlloc_6841_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(
    mut v_a_6843_: *mut LeanObject,
    mut v_a_6844_: *mut LeanObject,
    mut v_a_6845_: *mut LeanObject,
    mut v_a_6846_: *mut LeanObject,
    mut v_a_6847_: *mut LeanObject,
    mut v_a_6848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6849_: *mut LeanObject = core::ptr::null_mut();
    v_res_6849_ = l_Lean_Elab_ComputedFields_overrideCasesOn(
        v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_, v_a_6847_,
    );
    lean_dec(v_a_6847_);
    lean_dec_ref(v_a_6846_);
    lean_dec(v_a_6845_);
    lean_dec_ref(v_a_6844_);
    lean_dec_ref(v_a_6843_);
    return v_res_6849_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(
    mut v_inst_6850_: *mut LeanObject,
    mut v_R_6851_: *mut LeanObject,
    mut v_a_6852_: *mut LeanObject,
    mut v_b_6853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    v___x_6854_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_6852_, v_b_6853_);
    return v___x_6854_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(
    mut v_00_u03b1_6855_: *mut LeanObject,
    mut v_name_6856_: *mut LeanObject,
    mut v_bi_6857_: u8,
    mut v_type_6858_: *mut LeanObject,
    mut v_k_6859_: *mut LeanObject,
    mut v_kind_6860_: u8,
    mut v___y_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
    mut v___y_6863_: *mut LeanObject,
    mut v___y_6864_: *mut LeanObject,
    mut v___y_6865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    v___x_6867_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_6856_, v_bi_6857_, v_type_6858_, v_k_6859_, v_kind_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_);
    return v___x_6867_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(
    mut v_00_u03b1_6868_: *mut LeanObject,
    mut v_name_6869_: *mut LeanObject,
    mut v_bi_6870_: *mut LeanObject,
    mut v_type_6871_: *mut LeanObject,
    mut v_k_6872_: *mut LeanObject,
    mut v_kind_6873_: *mut LeanObject,
    mut v___y_6874_: *mut LeanObject,
    mut v___y_6875_: *mut LeanObject,
    mut v___y_6876_: *mut LeanObject,
    mut v___y_6877_: *mut LeanObject,
    mut v___y_6878_: *mut LeanObject,
    mut v___y_6879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_6880_: u8 = 0;
    let mut v_kind_boxed_6881_: u8 = 0;
    let mut v_res_6882_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_6880_ = (lean_unbox(v_bi_6870_) as u8);
    v_kind_boxed_6881_ = (lean_unbox(v_kind_6873_) as u8);
    v_res_6882_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_6868_, v_name_6869_, v_bi_boxed_6880_, v_type_6871_, v_k_6872_, v_kind_boxed_6881_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_);
    lean_dec(v___y_6878_);
    lean_dec_ref(v___y_6877_);
    lean_dec(v___y_6876_);
    lean_dec_ref(v___y_6875_);
    lean_dec_ref(v___y_6874_);
    return v_res_6882_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(
    mut v_00_u03b1_6883_: *mut LeanObject,
    mut v_name_6884_: *mut LeanObject,
    mut v_type_6885_: *mut LeanObject,
    mut v_k_6886_: *mut LeanObject,
    mut v___y_6887_: *mut LeanObject,
    mut v___y_6888_: *mut LeanObject,
    mut v___y_6889_: *mut LeanObject,
    mut v___y_6890_: *mut LeanObject,
    mut v___y_6891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    v___x_6893_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_6884_, v_type_6885_, v_k_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_);
    return v___x_6893_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(
    mut v_00_u03b1_6894_: *mut LeanObject,
    mut v_name_6895_: *mut LeanObject,
    mut v_type_6896_: *mut LeanObject,
    mut v_k_6897_: *mut LeanObject,
    mut v___y_6898_: *mut LeanObject,
    mut v___y_6899_: *mut LeanObject,
    mut v___y_6900_: *mut LeanObject,
    mut v___y_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6904_: *mut LeanObject = core::ptr::null_mut();
    v_res_6904_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(
            v_00_u03b1_6894_,
            v_name_6895_,
            v_type_6896_,
            v_k_6897_,
            v___y_6898_,
            v___y_6899_,
            v___y_6900_,
            v___y_6901_,
            v___y_6902_,
        );
    lean_dec(v___y_6902_);
    lean_dec_ref(v___y_6901_);
    lean_dec(v___y_6900_);
    lean_dec_ref(v___y_6899_);
    lean_dec_ref(v___y_6898_);
    return v_res_6904_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(
    mut v_env_6905_: *mut LeanObject,
    mut v___y_6906_: *mut LeanObject,
    mut v___y_6907_: *mut LeanObject,
    mut v___y_6908_: *mut LeanObject,
    mut v___y_6909_: *mut LeanObject,
    mut v___y_6910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    v___x_6912_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_6905_, v___y_6908_, v___y_6910_);
    return v___x_6912_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(
    mut v_env_6913_: *mut LeanObject,
    mut v___y_6914_: *mut LeanObject,
    mut v___y_6915_: *mut LeanObject,
    mut v___y_6916_: *mut LeanObject,
    mut v___y_6917_: *mut LeanObject,
    mut v___y_6918_: *mut LeanObject,
    mut v___y_6919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6920_: *mut LeanObject = core::ptr::null_mut();
    v_res_6920_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_6913_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_);
    lean_dec(v___y_6918_);
    lean_dec_ref(v___y_6917_);
    lean_dec(v___y_6916_);
    lean_dec_ref(v___y_6915_);
    lean_dec_ref(v___y_6914_);
    return v_res_6920_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(
    mut v___x_6921_: *mut LeanObject,
    mut v_sz_6922_: usize,
    mut v_i_6923_: usize,
    mut v_bs_6924_: *mut LeanObject,
    mut v___y_6925_: *mut LeanObject,
    mut v___y_6926_: *mut LeanObject,
    mut v___y_6927_: *mut LeanObject,
    mut v___y_6928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6930_: u8 = 0;
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: usize = 0;
    let mut v___x_6938_: usize = 0;
    let mut v___x_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6944_: u8 = 0;
    let mut v___x_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6930_ = lean_usize_dec_lt(v_i_6923_, v_sz_6922_);
                if v___x_6930_ == 0 {
                    lean_dec_ref(v___x_6921_);
                    v___x_6931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6931_, 0, v_bs_6924_);
                    return v___x_6931_;
                } else {
                    v_v_6932_ = lean_array_uget_borrowed(v_bs_6924_, v_i_6923_);
                    lean_inc_ref(v___x_6921_);
                    lean_inc(v_v_6932_);
                    v___x_6933_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(
                        v_v_6932_,
                        v___x_6921_,
                        v___y_6925_,
                        v___y_6926_,
                        v___y_6927_,
                        v___y_6928_,
                    );
                    if lean_obj_tag(v___x_6933_) == 0 {
                        v_a_6934_ = lean_ctor_get(v___x_6933_, 0);
                        lean_inc(v_a_6934_);
                        lean_dec_ref_known(v___x_6933_, 1);
                        v___x_6935_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6936_ = lean_array_uset(v_bs_6924_, v_i_6923_, v___x_6935_);
                        v___x_6937_ = 1usize;
                        v___x_6938_ = lean_usize_add(v_i_6923_, v___x_6937_);
                        v___x_6939_ = lean_array_uset(v_bs_x27_6936_, v_i_6923_, v_a_6934_);
                        v_i_6923_ = v___x_6938_;
                        v_bs_6924_ = v___x_6939_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_6924_);
                        lean_dec_ref(v___x_6921_);
                        v_a_6941_ = lean_ctor_get(v___x_6933_, 0);
                        v_isSharedCheck_6948_ = (!lean_is_exclusive(v___x_6933_)) as u8;
                        if v_isSharedCheck_6948_ == 0 {
                            v___x_6943_ = v___x_6933_;
                            v_isShared_6944_ = v_isSharedCheck_6948_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6941_);
                            lean_dec(v___x_6933_);
                            v___x_6943_ = lean_box(0);
                            v_isShared_6944_ = v_isSharedCheck_6948_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6944_ == 0 {
                    v___x_6946_ = v___x_6943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6947_, 0, v_a_6941_);
                    v___x_6946_ = v_reuseFailAlloc_6947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(
    mut v___x_6949_: *mut LeanObject,
    mut v_sz_6950_: *mut LeanObject,
    mut v_i_6951_: *mut LeanObject,
    mut v_bs_6952_: *mut LeanObject,
    mut v___y_6953_: *mut LeanObject,
    mut v___y_6954_: *mut LeanObject,
    mut v___y_6955_: *mut LeanObject,
    mut v___y_6956_: *mut LeanObject,
    mut v___y_6957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6958_: usize = 0;
    let mut v_i_boxed_6959_: usize = 0;
    let mut v_res_6960_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6958_ = lean_unbox_usize(v_sz_6950_);
    lean_dec(v_sz_6950_);
    v_i_boxed_6959_ = lean_unbox_usize(v_i_6951_);
    lean_dec(v_i_6951_);
    v_res_6960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_6949_, v_sz_boxed_6958_, v_i_boxed_6959_, v_bs_6952_, v___y_6953_, v___y_6954_, v___y_6955_, v___y_6956_);
    lean_dec(v___y_6956_);
    lean_dec_ref(v___y_6955_);
    lean_dec(v___y_6954_);
    lean_dec_ref(v___y_6953_);
    return v_res_6960_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(
    mut v_head_6961_: *mut LeanObject,
    mut v_compFields_6962_: *mut LeanObject,
    mut v___x_6963_: *mut LeanObject,
    mut v___y_6964_: *mut LeanObject,
    mut v___y_6965_: *mut LeanObject,
    mut v___y_6966_: *mut LeanObject,
    mut v___y_6967_: *mut LeanObject,
    mut v___y_6968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6974_: u8 = 0;
    let mut v___x_6975_: u8 = 0;
    let mut v_sz_6976_: usize = 0;
    let mut v___x_6977_: usize = 0;
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6983_: u8 = 0;
    let mut v_a_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6987_: u8 = 0;
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6970_ = l_Lean_Elab_ComputedFields_isScalarField(
                    v_head_6961_,
                    v___y_6967_,
                    v___y_6968_,
                );
                if lean_obj_tag(v___x_6970_) == 0 {
                    v_a_6971_ = lean_ctor_get(v___x_6970_, 0);
                    v_isSharedCheck_6983_ = (!lean_is_exclusive(v___x_6970_)) as u8;
                    if v_isSharedCheck_6983_ == 0 {
                        v___x_6973_ = v___x_6970_;
                        v_isShared_6974_ = v_isSharedCheck_6983_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6971_);
                        lean_dec(v___x_6970_);
                        v___x_6973_ = lean_box(0);
                        v_isShared_6974_ = v_isSharedCheck_6983_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_6963_);
                    lean_dec_ref(v_compFields_6962_);
                    v_a_6984_ = lean_ctor_get(v___x_6970_, 0);
                    v_isSharedCheck_6991_ = (!lean_is_exclusive(v___x_6970_)) as u8;
                    if v_isSharedCheck_6991_ == 0 {
                        v___x_6986_ = v___x_6970_;
                        v_isShared_6987_ = v_isSharedCheck_6991_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6984_);
                        lean_dec(v___x_6970_);
                        v___x_6986_ = lean_box(0);
                        v_isShared_6987_ = v_isSharedCheck_6991_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6975_ = (lean_unbox(v_a_6971_) as u8);
                lean_dec(v_a_6971_);
                if v___x_6975_ == 0 {
                    lean_del_object(v___x_6973_);
                    v_sz_6976_ = lean_array_size(v_compFields_6962_);
                    v___x_6977_ = 0usize;
                    v___x_6978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_6963_, v_sz_6976_, v___x_6977_, v_compFields_6962_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_);
                    return v___x_6978_;
                } else {
                    lean_dec_ref(v___x_6963_);
                    lean_dec_ref(v_compFields_6962_);
                    v___x_6979_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2;
                    if v_isShared_6974_ == 0 {
                        lean_ctor_set(v___x_6973_, 0, v___x_6979_);
                        v___x_6981_ = v___x_6973_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6982_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6982_, 0, v___x_6979_);
                        v___x_6981_ = v_reuseFailAlloc_6982_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6981_;
            }
            3 => {
                if v_isShared_6987_ == 0 {
                    v___x_6989_ = v___x_6986_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6990_, 0, v_a_6984_);
                    v___x_6989_ = v_reuseFailAlloc_6990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(
    mut v_head_6992_: *mut LeanObject,
    mut v_compFields_6993_: *mut LeanObject,
    mut v___x_6994_: *mut LeanObject,
    mut v___y_6995_: *mut LeanObject,
    mut v___y_6996_: *mut LeanObject,
    mut v___y_6997_: *mut LeanObject,
    mut v___y_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
    mut v___y_7000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7001_: *mut LeanObject = core::ptr::null_mut();
    v_res_7001_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_6992_, v_compFields_6993_, v___x_6994_, v___y_6995_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_);
    lean_dec(v___y_6999_);
    lean_dec_ref(v___y_6998_);
    lean_dec(v___y_6997_);
    lean_dec_ref(v___y_6996_);
    lean_dec_ref(v___y_6995_);
    return v_res_7001_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(
    mut v___y_7002_: *mut LeanObject,
    mut v_isExporting_7003_: u8,
    mut v___x_7004_: *mut LeanObject,
    mut v___y_7005_: *mut LeanObject,
    mut v___x_7006_: *mut LeanObject,
    mut v_a_x3f_7007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7020_: u8 = 0;
    let mut v___x_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7032_: u8 = 0;
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7039_: u8 = 0;
    let mut v_unused_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7042_: u8 = 0;
    let mut v_unused_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7009_ = lean_st_ref_take(v___y_7002_);
                v_env_7010_ = lean_ctor_get(v___x_7009_, 0);
                v_nextMacroScope_7011_ = lean_ctor_get(v___x_7009_, 1);
                v_ngen_7012_ = lean_ctor_get(v___x_7009_, 2);
                v_auxDeclNGen_7013_ = lean_ctor_get(v___x_7009_, 3);
                v_traceState_7014_ = lean_ctor_get(v___x_7009_, 4);
                v_messages_7015_ = lean_ctor_get(v___x_7009_, 6);
                v_infoState_7016_ = lean_ctor_get(v___x_7009_, 7);
                v_snapshotTasks_7017_ = lean_ctor_get(v___x_7009_, 8);
                v_isSharedCheck_7042_ = (!lean_is_exclusive(v___x_7009_)) as u8;
                if v_isSharedCheck_7042_ == 0 {
                    v_unused_7043_ = lean_ctor_get(v___x_7009_, 5);
                    lean_dec(v_unused_7043_);
                    v___x_7019_ = v___x_7009_;
                    v_isShared_7020_ = v_isSharedCheck_7042_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_7017_);
                    lean_inc(v_infoState_7016_);
                    lean_inc(v_messages_7015_);
                    lean_inc(v_traceState_7014_);
                    lean_inc(v_auxDeclNGen_7013_);
                    lean_inc(v_ngen_7012_);
                    lean_inc(v_nextMacroScope_7011_);
                    lean_inc(v_env_7010_);
                    lean_dec(v___x_7009_);
                    v___x_7019_ = lean_box(0);
                    v_isShared_7020_ = v_isSharedCheck_7042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7021_ = l_Lean_Environment_setExporting(v_env_7010_, v_isExporting_7003_);
                if v_isShared_7020_ == 0 {
                    lean_ctor_set(v___x_7019_, 5, v___x_7004_);
                    lean_ctor_set(v___x_7019_, 0, v___x_7021_);
                    v___x_7023_ = v___x_7019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7041_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 0, v___x_7021_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 1, v_nextMacroScope_7011_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 2, v_ngen_7012_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 3, v_auxDeclNGen_7013_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 4, v_traceState_7014_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 5, v___x_7004_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 6, v_messages_7015_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 7, v_infoState_7016_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 8, v_snapshotTasks_7017_);
                    v___x_7023_ = v_reuseFailAlloc_7041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7024_ = lean_st_ref_set(v___y_7002_, v___x_7023_);
                v___x_7025_ = lean_st_ref_take(v___y_7005_);
                v_mctx_7026_ = lean_ctor_get(v___x_7025_, 0);
                v_zetaDeltaFVarIds_7027_ = lean_ctor_get(v___x_7025_, 2);
                v_postponed_7028_ = lean_ctor_get(v___x_7025_, 3);
                v_diag_7029_ = lean_ctor_get(v___x_7025_, 4);
                v_isSharedCheck_7039_ = (!lean_is_exclusive(v___x_7025_)) as u8;
                if v_isSharedCheck_7039_ == 0 {
                    v_unused_7040_ = lean_ctor_get(v___x_7025_, 1);
                    lean_dec(v_unused_7040_);
                    v___x_7031_ = v___x_7025_;
                    v_isShared_7032_ = v_isSharedCheck_7039_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_7029_);
                    lean_inc(v_postponed_7028_);
                    lean_inc(v_zetaDeltaFVarIds_7027_);
                    lean_inc(v_mctx_7026_);
                    lean_dec(v___x_7025_);
                    v___x_7031_ = lean_box(0);
                    v_isShared_7032_ = v_isSharedCheck_7039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7032_ == 0 {
                    lean_ctor_set(v___x_7031_, 1, v___x_7006_);
                    v___x_7034_ = v___x_7031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7038_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 0, v_mctx_7026_);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 1, v___x_7006_);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 2, v_zetaDeltaFVarIds_7027_);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 3, v_postponed_7028_);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 4, v_diag_7029_);
                    v___x_7034_ = v_reuseFailAlloc_7038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7035_ = lean_st_ref_set(v___y_7005_, v___x_7034_);
                v___x_7036_ = lean_box(0);
                v___x_7037_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7037_, 0, v___x_7036_);
                return v___x_7037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(
    mut v___y_7044_: *mut LeanObject,
    mut v_isExporting_7045_: *mut LeanObject,
    mut v___x_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
    mut v___x_7048_: *mut LeanObject,
    mut v_a_x3f_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_7051_: u8 = 0;
    let mut v_res_7052_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_7051_ = (lean_unbox(v_isExporting_7045_) as u8);
    v_res_7052_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_7044_, v_isExporting_boxed_7051_, v___x_7046_, v___y_7047_, v___x_7048_, v_a_x3f_7049_);
    lean_dec(v_a_x3f_7049_);
    lean_dec(v___y_7047_);
    lean_dec(v___y_7044_);
    return v_res_7052_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(
    mut v_x_7053_: *mut LeanObject,
    mut v_isExporting_7054_: u8,
    mut v___y_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
    mut v___y_7057_: *mut LeanObject,
    mut v___y_7058_: *mut LeanObject,
    mut v___y_7059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_7063_: u8 = 0;
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7075_: u8 = 0;
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7088_: u8 = 0;
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7097_: u8 = 0;
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7103_: u8 = 0;
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7107_: u8 = 0;
    let mut v_unused_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7110_: u8 = 0;
    let mut v_a_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7116_: u8 = 0;
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7120_: u8 = 0;
    let mut v_unused_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7123_: u8 = 0;
    let mut v_unused_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7126_: u8 = 0;
    let mut v_unused_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7061_ = lean_st_ref_get(v___y_7059_);
                v_env_7062_ = lean_ctor_get(v___x_7061_, 0);
                lean_inc_ref(v_env_7062_);
                lean_dec(v___x_7061_);
                v_isExporting_7063_ = lean_ctor_get_uint8(
                    v_env_7062_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_7062_);
                v___x_7064_ = lean_st_ref_take(v___y_7059_);
                v_env_7065_ = lean_ctor_get(v___x_7064_, 0);
                v_nextMacroScope_7066_ = lean_ctor_get(v___x_7064_, 1);
                v_ngen_7067_ = lean_ctor_get(v___x_7064_, 2);
                v_auxDeclNGen_7068_ = lean_ctor_get(v___x_7064_, 3);
                v_traceState_7069_ = lean_ctor_get(v___x_7064_, 4);
                v_messages_7070_ = lean_ctor_get(v___x_7064_, 6);
                v_infoState_7071_ = lean_ctor_get(v___x_7064_, 7);
                v_snapshotTasks_7072_ = lean_ctor_get(v___x_7064_, 8);
                v_isSharedCheck_7126_ = (!lean_is_exclusive(v___x_7064_)) as u8;
                if v_isSharedCheck_7126_ == 0 {
                    v_unused_7127_ = lean_ctor_get(v___x_7064_, 5);
                    lean_dec(v_unused_7127_);
                    v___x_7074_ = v___x_7064_;
                    v_isShared_7075_ = v_isSharedCheck_7126_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_7072_);
                    lean_inc(v_infoState_7071_);
                    lean_inc(v_messages_7070_);
                    lean_inc(v_traceState_7069_);
                    lean_inc(v_auxDeclNGen_7068_);
                    lean_inc(v_ngen_7067_);
                    lean_inc(v_nextMacroScope_7066_);
                    lean_inc(v_env_7065_);
                    lean_dec(v___x_7064_);
                    v___x_7074_ = lean_box(0);
                    v_isShared_7075_ = v_isSharedCheck_7126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7076_ = l_Lean_Environment_setExporting(v_env_7065_, v_isExporting_7054_);
                v___x_7077_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
                if v_isShared_7075_ == 0 {
                    lean_ctor_set(v___x_7074_, 5, v___x_7077_);
                    lean_ctor_set(v___x_7074_, 0, v___x_7076_);
                    v___x_7079_ = v___x_7074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7125_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 0, v___x_7076_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 1, v_nextMacroScope_7066_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 2, v_ngen_7067_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 3, v_auxDeclNGen_7068_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 4, v_traceState_7069_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 5, v___x_7077_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 6, v_messages_7070_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 7, v_infoState_7071_);
                    lean_ctor_set(v_reuseFailAlloc_7125_, 8, v_snapshotTasks_7072_);
                    v___x_7079_ = v_reuseFailAlloc_7125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7080_ = lean_st_ref_set(v___y_7059_, v___x_7079_);
                v___x_7081_ = lean_st_ref_take(v___y_7057_);
                v_mctx_7082_ = lean_ctor_get(v___x_7081_, 0);
                v_zetaDeltaFVarIds_7083_ = lean_ctor_get(v___x_7081_, 2);
                v_postponed_7084_ = lean_ctor_get(v___x_7081_, 3);
                v_diag_7085_ = lean_ctor_get(v___x_7081_, 4);
                v_isSharedCheck_7123_ = (!lean_is_exclusive(v___x_7081_)) as u8;
                if v_isSharedCheck_7123_ == 0 {
                    v_unused_7124_ = lean_ctor_get(v___x_7081_, 1);
                    lean_dec(v_unused_7124_);
                    v___x_7087_ = v___x_7081_;
                    v_isShared_7088_ = v_isSharedCheck_7123_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_7085_);
                    lean_inc(v_postponed_7084_);
                    lean_inc(v_zetaDeltaFVarIds_7083_);
                    lean_inc(v_mctx_7082_);
                    lean_dec(v___x_7081_);
                    v___x_7087_ = lean_box(0);
                    v_isShared_7088_ = v_isSharedCheck_7123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7089_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
                if v_isShared_7088_ == 0 {
                    lean_ctor_set(v___x_7087_, 1, v___x_7089_);
                    v___x_7091_ = v___x_7087_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7122_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7122_, 0, v_mctx_7082_);
                    lean_ctor_set(v_reuseFailAlloc_7122_, 1, v___x_7089_);
                    lean_ctor_set(v_reuseFailAlloc_7122_, 2, v_zetaDeltaFVarIds_7083_);
                    lean_ctor_set(v_reuseFailAlloc_7122_, 3, v_postponed_7084_);
                    lean_ctor_set(v_reuseFailAlloc_7122_, 4, v_diag_7085_);
                    v___x_7091_ = v_reuseFailAlloc_7122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7092_ = lean_st_ref_set(v___y_7057_, v___x_7091_);
                lean_inc(v___y_7059_);
                lean_inc_ref(v___y_7058_);
                lean_inc(v___y_7057_);
                lean_inc_ref(v___y_7056_);
                lean_inc_ref(v___y_7055_);
                v_r_7093_ = lean_apply_6(
                    v_x_7053_,
                    v___y_7055_,
                    v___y_7056_,
                    v___y_7057_,
                    v___y_7058_,
                    v___y_7059_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_7093_) == 0 {
                    v_a_7094_ = lean_ctor_get(v_r_7093_, 0);
                    v_isSharedCheck_7110_ = (!lean_is_exclusive(v_r_7093_)) as u8;
                    if v_isSharedCheck_7110_ == 0 {
                        v___x_7096_ = v_r_7093_;
                        v_isShared_7097_ = v_isSharedCheck_7110_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7094_);
                        lean_dec(v_r_7093_);
                        v___x_7096_ = lean_box(0);
                        v_isShared_7097_ = v_isSharedCheck_7110_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_7111_ = lean_ctor_get(v_r_7093_, 0);
                    lean_inc(v_a_7111_);
                    lean_dec_ref_known(v_r_7093_, 1);
                    v___x_7112_ = lean_box(0);
                    v___x_7113_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_7059_, v_isExporting_7063_, v___x_7077_, v___y_7057_, v___x_7089_, v___x_7112_);
                    v_isSharedCheck_7120_ = (!lean_is_exclusive(v___x_7113_)) as u8;
                    if v_isSharedCheck_7120_ == 0 {
                        v_unused_7121_ = lean_ctor_get(v___x_7113_, 0);
                        lean_dec(v_unused_7121_);
                        v___x_7115_ = v___x_7113_;
                        v_isShared_7116_ = v_isSharedCheck_7120_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_7113_);
                        v___x_7115_ = lean_box(0);
                        v_isShared_7116_ = v_isSharedCheck_7120_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_7094_);
                if v_isShared_7097_ == 0 {
                    lean_ctor_set_tag(v___x_7096_, 1);
                    v___x_7099_ = v___x_7096_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7109_, 0, v_a_7094_);
                    v___x_7099_ = v_reuseFailAlloc_7109_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7100_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_7059_, v_isExporting_7063_, v___x_7077_, v___y_7057_, v___x_7089_, v___x_7099_);
                lean_dec_ref(v___x_7099_);
                v_isSharedCheck_7107_ = (!lean_is_exclusive(v___x_7100_)) as u8;
                if v_isSharedCheck_7107_ == 0 {
                    v_unused_7108_ = lean_ctor_get(v___x_7100_, 0);
                    lean_dec(v_unused_7108_);
                    v___x_7102_ = v___x_7100_;
                    v_isShared_7103_ = v_isSharedCheck_7107_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___x_7100_);
                    v___x_7102_ = lean_box(0);
                    v_isShared_7103_ = v_isSharedCheck_7107_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_7103_ == 0 {
                    lean_ctor_set(v___x_7102_, 0, v_a_7094_);
                    v___x_7105_ = v___x_7102_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7106_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7106_, 0, v_a_7094_);
                    v___x_7105_ = v_reuseFailAlloc_7106_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7105_;
            }
            9 => {
                if v_isShared_7116_ == 0 {
                    lean_ctor_set_tag(v___x_7115_, 1);
                    lean_ctor_set(v___x_7115_, 0, v_a_7111_);
                    v___x_7118_ = v___x_7115_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7119_, 0, v_a_7111_);
                    v___x_7118_ = v_reuseFailAlloc_7119_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(
    mut v_x_7128_: *mut LeanObject,
    mut v_isExporting_7129_: *mut LeanObject,
    mut v___y_7130_: *mut LeanObject,
    mut v___y_7131_: *mut LeanObject,
    mut v___y_7132_: *mut LeanObject,
    mut v___y_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_7136_: u8 = 0;
    let mut v_res_7137_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_7136_ = (lean_unbox(v_isExporting_7129_) as u8);
    v_res_7137_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_7128_, v_isExporting_boxed_7136_, v___y_7130_, v___y_7131_, v___y_7132_, v___y_7133_, v___y_7134_);
    lean_dec(v___y_7134_);
    lean_dec_ref(v___y_7133_);
    lean_dec(v___y_7132_);
    lean_dec_ref(v___y_7131_);
    lean_dec_ref(v___y_7130_);
    return v_res_7137_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(
    mut v_x_7138_: *mut LeanObject,
    mut v_when_7139_: u8,
    mut v___y_7140_: *mut LeanObject,
    mut v___y_7141_: *mut LeanObject,
    mut v___y_7142_: *mut LeanObject,
    mut v___y_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_7139_ == 0 {
        let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_7144_);
        lean_inc_ref(v___y_7143_);
        lean_inc(v___y_7142_);
        lean_inc_ref(v___y_7141_);
        lean_inc_ref(v___y_7140_);
        v___x_7146_ = lean_apply_6(
            v_x_7138_,
            v___y_7140_,
            v___y_7141_,
            v___y_7142_,
            v___y_7143_,
            v___y_7144_,
            lean_box(0),
        );
        return v___x_7146_;
    } else {
        let mut v___x_7147_: u8 = 0;
        let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
        v___x_7147_ = 0;
        v___x_7148_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_7138_, v___x_7147_, v___y_7140_, v___y_7141_, v___y_7142_, v___y_7143_, v___y_7144_);
        return v___x_7148_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(
    mut v_x_7149_: *mut LeanObject,
    mut v_when_7150_: *mut LeanObject,
    mut v___y_7151_: *mut LeanObject,
    mut v___y_7152_: *mut LeanObject,
    mut v___y_7153_: *mut LeanObject,
    mut v___y_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_7157_: u8 = 0;
    let mut v_res_7158_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_7157_ = (lean_unbox(v_when_7150_) as u8);
    v_res_7158_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_7149_, v_when_boxed_7157_, v___y_7151_, v___y_7152_, v___y_7153_, v___y_7154_, v___y_7155_);
    lean_dec(v___y_7155_);
    lean_dec_ref(v___y_7154_);
    lean_dec(v___y_7153_);
    lean_dec_ref(v___y_7152_);
    lean_dec_ref(v___y_7151_);
    return v_res_7158_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(
    mut v_params_7159_: *mut LeanObject,
    mut v___x_7160_: *mut LeanObject,
    mut v_head_7161_: *mut LeanObject,
    mut v_compFields_7162_: *mut LeanObject,
    mut v_lparams_7163_: *mut LeanObject,
    mut v_levelParams_7164_: *mut LeanObject,
    mut v___x_7165_: *mut LeanObject,
    mut v_fields_7166_: *mut LeanObject,
    mut v_retTy_7167_: *mut LeanObject,
    mut v___y_7168_: *mut LeanObject,
    mut v___y_7169_: *mut LeanObject,
    mut v___y_7170_: *mut LeanObject,
    mut v___y_7171_: *mut LeanObject,
    mut v___y_7172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: u8 = 0;
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: u8 = 0;
    let mut v___x_7191_: u8 = 0;
    let mut v___x_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: u8 = 0;
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7209_: u8 = 0;
    let mut v___x_7210_: u8 = 0;
    let mut v___x_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: u8 = 0;
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7216_: u8 = 0;
    let mut v_a_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7220_: u8 = 0;
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7224_: u8 = 0;
    let mut v_a_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7228_: u8 = 0;
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7232_: u8 = 0;
    let mut v_a_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7236_: u8 = 0;
    let mut v___x_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7240_: u8 = 0;
    let mut v_a_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7244_: u8 = 0;
    let mut v___x_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut v_a_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7252_: u8 = 0;
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_params_7159_);
                v___x_7174_ = l_Array_append___redArg(v_params_7159_, v_fields_7166_);
                lean_inc_ref(v___x_7160_);
                v___x_7175_ = l_Lean_mkAppN(v___x_7160_, v___x_7174_);
                lean_inc(v_head_7161_);
                v___f_7176_ = lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_7176_, 0, v_head_7161_);
                lean_closure_set(v___f_7176_, 1, v_compFields_7162_);
                lean_closure_set(v___f_7176_, 2, v___x_7175_);
                v___x_7177_ = 1;
                v___x_7178_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_7176_, v___x_7177_, v___y_7168_, v___y_7169_, v___y_7170_, v___y_7171_, v___y_7172_);
                if lean_obj_tag(v___x_7178_) == 0 {
                    v_a_7179_ = lean_ctor_get(v___x_7178_, 0);
                    lean_inc(v_a_7179_);
                    lean_dec_ref_known(v___x_7178_, 1);
                    lean_inc(v___y_7172_);
                    lean_inc_ref(v___y_7171_);
                    lean_inc(v___y_7170_);
                    lean_inc_ref(v___y_7169_);
                    v___x_7180_ = lean_infer_type(
                        v___x_7160_,
                        v___y_7169_,
                        v___y_7170_,
                        v___y_7171_,
                        v___y_7172_,
                    );
                    if lean_obj_tag(v___x_7180_) == 0 {
                        v_a_7181_ = lean_ctor_get(v___x_7180_, 0);
                        lean_inc(v_a_7181_);
                        lean_dec_ref_known(v___x_7180_, 1);
                        v___x_7182_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1;
                        lean_inc(v_head_7161_);
                        v___x_7183_ = l_Lean_Name_append(v_head_7161_, v___x_7182_);
                        v___x_7184_ = l_Lean_mkConst(v___x_7183_, v_lparams_7163_);
                        v___x_7185_ = l_Array_append___redArg(v_params_7159_, v_a_7179_);
                        lean_dec(v_a_7179_);
                        v___x_7186_ = l_Array_append___redArg(v___x_7185_, v_fields_7166_);
                        v___x_7187_ = l_Lean_mkAppN(v___x_7184_, v___x_7186_);
                        lean_dec_ref(v___x_7186_);
                        v___x_7188_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
                            v_retTy_7167_,
                            v___x_7187_,
                            v___y_7169_,
                            v___y_7170_,
                            v___y_7171_,
                            v___y_7172_,
                        );
                        if lean_obj_tag(v___x_7188_) == 0 {
                            v_a_7189_ = lean_ctor_get(v___x_7188_, 0);
                            lean_inc(v_a_7189_);
                            lean_dec_ref_known(v___x_7188_, 1);
                            v___x_7190_ = 0;
                            v___x_7191_ = 1;
                            v___x_7192_ = l_Lean_Meta_mkLambdaFVars(
                                v___x_7174_,
                                v_a_7189_,
                                v___x_7190_,
                                v___x_7177_,
                                v___x_7190_,
                                v___x_7177_,
                                v___x_7191_,
                                v___y_7169_,
                                v___y_7170_,
                                v___y_7171_,
                                v___y_7172_,
                            );
                            lean_dec_ref(v___x_7174_);
                            if lean_obj_tag(v___x_7192_) == 0 {
                                v_a_7193_ = lean_ctor_get(v___x_7192_, 0);
                                lean_inc(v_a_7193_);
                                lean_dec_ref_known(v___x_7192_, 1);
                                v___x_7194_ =
                                    l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                                lean_inc(v_head_7161_);
                                v___x_7195_ = l_Lean_Name_append(v_head_7161_, v___x_7194_);
                                lean_inc_n(v___x_7195_, 2);
                                v___x_7196_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_7196_, 0, v___x_7195_);
                                lean_ctor_set(v___x_7196_, 1, v_levelParams_7164_);
                                lean_ctor_set(v___x_7196_, 2, v_a_7181_);
                                v___x_7197_ = lean_box(0);
                                v___x_7198_ = 0;
                                v___x_7199_ = lean_box(0);
                                v___x_7200_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_7200_, 0, v___x_7195_);
                                lean_ctor_set(v___x_7200_, 1, v___x_7199_);
                                v___x_7201_ = lean_alloc_ctor(0, 4, (1) as u32);
                                lean_ctor_set(v___x_7201_, 0, v___x_7196_);
                                lean_ctor_set(v___x_7201_, 1, v_a_7193_);
                                lean_ctor_set(v___x_7201_, 2, v___x_7197_);
                                lean_ctor_set(v___x_7201_, 3, v___x_7200_);
                                lean_ctor_set_uint8(
                                    v___x_7201_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v___x_7198_,
                                );
                                v___x_7202_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_7202_, 0, v___x_7201_);
                                v___x_7203_ = l_Lean_addDecl(
                                    v___x_7202_,
                                    v___x_7190_,
                                    v___y_7171_,
                                    v___y_7172_,
                                );
                                if lean_obj_tag(v___x_7203_) == 0 {
                                    lean_dec_ref_known(v___x_7203_, 1);
                                    lean_inc(v___x_7195_);
                                    lean_inc(v_head_7161_);
                                    v___x_7204_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_7161_, v___x_7195_, v___y_7168_, v___y_7169_, v___y_7170_, v___y_7171_, v___y_7172_);
                                    if lean_obj_tag(v___x_7204_) == 0 {
                                        lean_dec_ref_known(v___x_7204_, 1);
                                        v___x_7205_ = l_Lean_Elab_ComputedFields_isScalarField(
                                            v_head_7161_,
                                            v___y_7171_,
                                            v___y_7172_,
                                        );
                                        if lean_obj_tag(v___x_7205_) == 0 {
                                            v_a_7206_ = lean_ctor_get(v___x_7205_, 0);
                                            v_isSharedCheck_7216_ =
                                                (!lean_is_exclusive(v___x_7205_)) as u8;
                                            if v_isSharedCheck_7216_ == 0 {
                                                v___x_7208_ = v___x_7205_;
                                                v_isShared_7209_ = v_isSharedCheck_7216_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7206_);
                                                lean_dec(v___x_7205_);
                                                v___x_7208_ = lean_box(0);
                                                v_isShared_7209_ = v_isSharedCheck_7216_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_7195_);
                                            v_a_7217_ = lean_ctor_get(v___x_7205_, 0);
                                            v_isSharedCheck_7224_ =
                                                (!lean_is_exclusive(v___x_7205_)) as u8;
                                            if v_isSharedCheck_7224_ == 0 {
                                                v___x_7219_ = v___x_7205_;
                                                v_isShared_7220_ = v_isSharedCheck_7224_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7217_);
                                                lean_dec(v___x_7205_);
                                                v___x_7219_ = lean_box(0);
                                                v_isShared_7220_ = v_isSharedCheck_7224_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_7195_);
                                        lean_dec(v_head_7161_);
                                        return v___x_7204_;
                                    }
                                } else {
                                    lean_dec(v___x_7195_);
                                    lean_dec(v_head_7161_);
                                    return v___x_7203_;
                                }
                            } else {
                                lean_dec(v_a_7181_);
                                lean_dec(v_levelParams_7164_);
                                lean_dec(v_head_7161_);
                                v_a_7225_ = lean_ctor_get(v___x_7192_, 0);
                                v_isSharedCheck_7232_ = (!lean_is_exclusive(v___x_7192_)) as u8;
                                if v_isSharedCheck_7232_ == 0 {
                                    v___x_7227_ = v___x_7192_;
                                    v_isShared_7228_ = v_isSharedCheck_7232_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_7225_);
                                    lean_dec(v___x_7192_);
                                    v___x_7227_ = lean_box(0);
                                    v_isShared_7228_ = v_isSharedCheck_7232_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7181_);
                            lean_dec_ref(v___x_7174_);
                            lean_dec(v_levelParams_7164_);
                            lean_dec(v_head_7161_);
                            v_a_7233_ = lean_ctor_get(v___x_7188_, 0);
                            v_isSharedCheck_7240_ = (!lean_is_exclusive(v___x_7188_)) as u8;
                            if v_isSharedCheck_7240_ == 0 {
                                v___x_7235_ = v___x_7188_;
                                v_isShared_7236_ = v_isSharedCheck_7240_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_7233_);
                                lean_dec(v___x_7188_);
                                v___x_7235_ = lean_box(0);
                                v_isShared_7236_ = v_isSharedCheck_7240_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_7179_);
                        lean_dec_ref(v___x_7174_);
                        lean_dec_ref(v_retTy_7167_);
                        lean_dec(v_levelParams_7164_);
                        lean_dec(v_lparams_7163_);
                        lean_dec(v_head_7161_);
                        lean_dec_ref(v_params_7159_);
                        v_a_7241_ = lean_ctor_get(v___x_7180_, 0);
                        v_isSharedCheck_7248_ = (!lean_is_exclusive(v___x_7180_)) as u8;
                        if v_isSharedCheck_7248_ == 0 {
                            v___x_7243_ = v___x_7180_;
                            v_isShared_7244_ = v_isSharedCheck_7248_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7241_);
                            lean_dec(v___x_7180_);
                            v___x_7243_ = lean_box(0);
                            v_isShared_7244_ = v_isSharedCheck_7248_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_7174_);
                    lean_dec_ref(v_retTy_7167_);
                    lean_dec(v_levelParams_7164_);
                    lean_dec(v_lparams_7163_);
                    lean_dec(v_head_7161_);
                    lean_dec_ref(v___x_7160_);
                    lean_dec_ref(v_params_7159_);
                    v_a_7249_ = lean_ctor_get(v___x_7178_, 0);
                    v_isSharedCheck_7256_ = (!lean_is_exclusive(v___x_7178_)) as u8;
                    if v_isSharedCheck_7256_ == 0 {
                        v___x_7251_ = v___x_7178_;
                        v_isShared_7252_ = v_isSharedCheck_7256_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_7249_);
                        lean_dec(v___x_7178_);
                        v___x_7251_ = lean_box(0);
                        v_isShared_7252_ = v_isSharedCheck_7256_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7210_ = (lean_unbox(v_a_7206_) as u8);
                lean_dec(v_a_7206_);
                if v___x_7210_ == 0 {
                    lean_dec(v___x_7195_);
                    if v_isShared_7209_ == 0 {
                        lean_ctor_set(v___x_7208_, 0, v___x_7165_);
                        v___x_7212_ = v___x_7208_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7213_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7213_, 0, v___x_7165_);
                        v___x_7212_ = v_reuseFailAlloc_7213_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7208_);
                    v___x_7214_ = 0;
                    v___x_7215_ = l_Lean_Meta_setInlineAttribute(
                        v___x_7195_,
                        v___x_7214_,
                        v___y_7169_,
                        v___y_7170_,
                        v___y_7171_,
                        v___y_7172_,
                    );
                    return v___x_7215_;
                }
            }
            2 => {
                return v___x_7212_;
            }
            3 => {
                if v_isShared_7220_ == 0 {
                    v___x_7222_ = v___x_7219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7223_, 0, v_a_7217_);
                    v___x_7222_ = v_reuseFailAlloc_7223_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7222_;
            }
            5 => {
                if v_isShared_7228_ == 0 {
                    v___x_7230_ = v___x_7227_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7231_, 0, v_a_7225_);
                    v___x_7230_ = v_reuseFailAlloc_7231_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7230_;
            }
            7 => {
                if v_isShared_7236_ == 0 {
                    v___x_7238_ = v___x_7235_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7239_, 0, v_a_7233_);
                    v___x_7238_ = v_reuseFailAlloc_7239_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7238_;
            }
            9 => {
                if v_isShared_7244_ == 0 {
                    v___x_7246_ = v___x_7243_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7247_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7247_, 0, v_a_7241_);
                    v___x_7246_ = v_reuseFailAlloc_7247_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7246_;
            }
            11 => {
                if v_isShared_7252_ == 0 {
                    v___x_7254_ = v___x_7251_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7255_, 0, v_a_7249_);
                    v___x_7254_ = v_reuseFailAlloc_7255_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(
    mut v_params_7257_: *mut LeanObject,
    mut v___x_7258_: *mut LeanObject,
    mut v_head_7259_: *mut LeanObject,
    mut v_compFields_7260_: *mut LeanObject,
    mut v_lparams_7261_: *mut LeanObject,
    mut v_levelParams_7262_: *mut LeanObject,
    mut v___x_7263_: *mut LeanObject,
    mut v_fields_7264_: *mut LeanObject,
    mut v_retTy_7265_: *mut LeanObject,
    mut v___y_7266_: *mut LeanObject,
    mut v___y_7267_: *mut LeanObject,
    mut v___y_7268_: *mut LeanObject,
    mut v___y_7269_: *mut LeanObject,
    mut v___y_7270_: *mut LeanObject,
    mut v___y_7271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7272_: *mut LeanObject = core::ptr::null_mut();
    v_res_7272_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_7257_, v___x_7258_, v_head_7259_, v_compFields_7260_, v_lparams_7261_, v_levelParams_7262_, v___x_7263_, v_fields_7264_, v_retTy_7265_, v___y_7266_, v___y_7267_, v___y_7268_, v___y_7269_, v___y_7270_);
    lean_dec(v___y_7270_);
    lean_dec_ref(v___y_7269_);
    lean_dec(v___y_7268_);
    lean_dec_ref(v___y_7267_);
    lean_dec_ref(v___y_7266_);
    lean_dec_ref(v_fields_7264_);
    return v_res_7272_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(
    mut v_lparams_7273_: *mut LeanObject,
    mut v_params_7274_: *mut LeanObject,
    mut v_compFields_7275_: *mut LeanObject,
    mut v_levelParams_7276_: *mut LeanObject,
    mut v_as_x27_7277_: *mut LeanObject,
    mut v_b_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
    mut v___y_7280_: *mut LeanObject,
    mut v___y_7281_: *mut LeanObject,
    mut v___y_7282_: *mut LeanObject,
    mut v___y_7283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: u8 = 0;
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7300_: u8 = 0;
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_7277_) == 0 {
                    lean_dec(v_levelParams_7276_);
                    lean_dec_ref(v_compFields_7275_);
                    lean_dec_ref(v_params_7274_);
                    lean_dec(v_lparams_7273_);
                    v___x_7285_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7285_, 0, v_b_7278_);
                    return v___x_7285_;
                } else {
                    v_head_7286_ = lean_ctor_get(v_as_x27_7277_, 0);
                    v_tail_7287_ = lean_ctor_get(v_as_x27_7277_, 1);
                    lean_inc(v_lparams_7273_);
                    lean_inc(v_head_7286_);
                    v___x_7288_ = l_Lean_mkConst(v_head_7286_, v_lparams_7273_);
                    lean_inc_ref(v___x_7288_);
                    v___x_7289_ = l_Lean_mkAppN(v___x_7288_, v_params_7274_);
                    lean_inc(v___y_7283_);
                    lean_inc_ref(v___y_7282_);
                    lean_inc(v___y_7281_);
                    lean_inc_ref(v___y_7280_);
                    v___x_7290_ = lean_infer_type(
                        v___x_7289_,
                        v___y_7280_,
                        v___y_7281_,
                        v___y_7282_,
                        v___y_7283_,
                    );
                    if lean_obj_tag(v___x_7290_) == 0 {
                        v_a_7291_ = lean_ctor_get(v___x_7290_, 0);
                        lean_inc(v_a_7291_);
                        lean_dec_ref_known(v___x_7290_, 1);
                        v___x_7292_ = lean_box(0);
                        lean_inc(v_levelParams_7276_);
                        lean_inc(v_lparams_7273_);
                        lean_inc_ref(v_compFields_7275_);
                        lean_inc(v_head_7286_);
                        lean_inc_ref(v_params_7274_);
                        v___f_7293_ = lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed as *mut core::ffi::c_void, 15, 7);
                        lean_closure_set(v___f_7293_, 0, v_params_7274_);
                        lean_closure_set(v___f_7293_, 1, v___x_7288_);
                        lean_closure_set(v___f_7293_, 2, v_head_7286_);
                        lean_closure_set(v___f_7293_, 3, v_compFields_7275_);
                        lean_closure_set(v___f_7293_, 4, v_lparams_7273_);
                        lean_closure_set(v___f_7293_, 5, v_levelParams_7276_);
                        lean_closure_set(v___f_7293_, 6, v___x_7292_);
                        v___x_7294_ = 0;
                        v___x_7295_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_7291_, v___f_7293_, v___x_7294_, v___y_7279_, v___y_7280_, v___y_7281_, v___y_7282_, v___y_7283_);
                        if lean_obj_tag(v___x_7295_) == 0 {
                            lean_dec_ref_known(v___x_7295_, 1);
                            v_as_x27_7277_ = v_tail_7287_;
                            v_b_7278_ = v___x_7292_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_levelParams_7276_);
                            lean_dec_ref(v_compFields_7275_);
                            lean_dec_ref(v_params_7274_);
                            lean_dec(v_lparams_7273_);
                            return v___x_7295_;
                        }
                    } else {
                        lean_dec_ref(v___x_7288_);
                        lean_dec(v_levelParams_7276_);
                        lean_dec_ref(v_compFields_7275_);
                        lean_dec_ref(v_params_7274_);
                        lean_dec(v_lparams_7273_);
                        v_a_7297_ = lean_ctor_get(v___x_7290_, 0);
                        v_isSharedCheck_7304_ = (!lean_is_exclusive(v___x_7290_)) as u8;
                        if v_isSharedCheck_7304_ == 0 {
                            v___x_7299_ = v___x_7290_;
                            v_isShared_7300_ = v_isSharedCheck_7304_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7297_);
                            lean_dec(v___x_7290_);
                            v___x_7299_ = lean_box(0);
                            v_isShared_7300_ = v_isSharedCheck_7304_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7300_ == 0 {
                    v___x_7302_ = v___x_7299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7303_, 0, v_a_7297_);
                    v___x_7302_ = v_reuseFailAlloc_7303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(
    mut v_lparams_7305_: *mut LeanObject,
    mut v_params_7306_: *mut LeanObject,
    mut v_compFields_7307_: *mut LeanObject,
    mut v_levelParams_7308_: *mut LeanObject,
    mut v_as_x27_7309_: *mut LeanObject,
    mut v_b_7310_: *mut LeanObject,
    mut v___y_7311_: *mut LeanObject,
    mut v___y_7312_: *mut LeanObject,
    mut v___y_7313_: *mut LeanObject,
    mut v___y_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
    mut v___y_7316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7317_: *mut LeanObject = core::ptr::null_mut();
    v_res_7317_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_7305_, v_params_7306_, v_compFields_7307_, v_levelParams_7308_, v_as_x27_7309_, v_b_7310_, v___y_7311_, v___y_7312_, v___y_7313_, v___y_7314_, v___y_7315_);
    lean_dec(v___y_7315_);
    lean_dec_ref(v___y_7314_);
    lean_dec(v___y_7313_);
    lean_dec_ref(v___y_7312_);
    lean_dec_ref(v___y_7311_);
    lean_dec(v_as_x27_7309_);
    return v_res_7317_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideConstructors(
    mut v_a_7318_: *mut LeanObject,
    mut v_a_7319_: *mut LeanObject,
    mut v_a_7320_: *mut LeanObject,
    mut v_a_7321_: *mut LeanObject,
    mut v_a_7322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInductiveVal_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lparams_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_7327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_compFields_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_7330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7335_: u8 = 0;
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7339_: u8 = 0;
    let mut v_unused_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInductiveVal_7324_ = lean_ctor_get(v_a_7318_, 0);
                v_toConstantVal_7325_ = lean_ctor_get(v_toInductiveVal_7324_, 0);
                v_lparams_7326_ = lean_ctor_get(v_a_7318_, 1);
                v_params_7327_ = lean_ctor_get(v_a_7318_, 2);
                v_compFields_7328_ = lean_ctor_get(v_a_7318_, 3);
                v_ctors_7329_ = lean_ctor_get(v_toInductiveVal_7324_, 4);
                v_levelParams_7330_ = lean_ctor_get(v_toConstantVal_7325_, 1);
                v___x_7331_ = lean_box(0);
                lean_inc(v_levelParams_7330_);
                lean_inc_ref(v_compFields_7328_);
                lean_inc_ref(v_params_7327_);
                lean_inc(v_lparams_7326_);
                v___x_7332_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_7326_, v_params_7327_, v_compFields_7328_, v_levelParams_7330_, v_ctors_7329_, v___x_7331_, v_a_7318_, v_a_7319_, v_a_7320_, v_a_7321_, v_a_7322_);
                if lean_obj_tag(v___x_7332_) == 0 {
                    v_isSharedCheck_7339_ = (!lean_is_exclusive(v___x_7332_)) as u8;
                    if v_isSharedCheck_7339_ == 0 {
                        v_unused_7340_ = lean_ctor_get(v___x_7332_, 0);
                        lean_dec(v_unused_7340_);
                        v___x_7334_ = v___x_7332_;
                        v_isShared_7335_ = v_isSharedCheck_7339_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_7332_);
                        v___x_7334_ = lean_box(0);
                        v_isShared_7335_ = v_isSharedCheck_7339_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_7332_;
                }
            }
            1 => {
                if v_isShared_7335_ == 0 {
                    lean_ctor_set(v___x_7334_, 0, v___x_7331_);
                    v___x_7337_ = v___x_7334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7338_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7338_, 0, v___x_7331_);
                    v___x_7337_ = v_reuseFailAlloc_7338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideConstructors___boxed(
    mut v_a_7341_: *mut LeanObject,
    mut v_a_7342_: *mut LeanObject,
    mut v_a_7343_: *mut LeanObject,
    mut v_a_7344_: *mut LeanObject,
    mut v_a_7345_: *mut LeanObject,
    mut v_a_7346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7347_: *mut LeanObject = core::ptr::null_mut();
    v_res_7347_ = l_Lean_Elab_ComputedFields_overrideConstructors(
        v_a_7341_, v_a_7342_, v_a_7343_, v_a_7344_, v_a_7345_,
    );
    lean_dec(v_a_7345_);
    lean_dec_ref(v_a_7344_);
    lean_dec(v_a_7343_);
    lean_dec_ref(v_a_7342_);
    lean_dec_ref(v_a_7341_);
    return v_res_7347_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(
    mut v___x_7348_: *mut LeanObject,
    mut v_sz_7349_: usize,
    mut v_i_7350_: usize,
    mut v_bs_7351_: *mut LeanObject,
    mut v___y_7352_: *mut LeanObject,
    mut v___y_7353_: *mut LeanObject,
    mut v___y_7354_: *mut LeanObject,
    mut v___y_7355_: *mut LeanObject,
    mut v___y_7356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    v___x_7358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_7348_, v_sz_7349_, v_i_7350_, v_bs_7351_, v___y_7353_, v___y_7354_, v___y_7355_, v___y_7356_);
    return v___x_7358_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(
    mut v___x_7359_: *mut LeanObject,
    mut v_sz_7360_: *mut LeanObject,
    mut v_i_7361_: *mut LeanObject,
    mut v_bs_7362_: *mut LeanObject,
    mut v___y_7363_: *mut LeanObject,
    mut v___y_7364_: *mut LeanObject,
    mut v___y_7365_: *mut LeanObject,
    mut v___y_7366_: *mut LeanObject,
    mut v___y_7367_: *mut LeanObject,
    mut v___y_7368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7369_: usize = 0;
    let mut v_i_boxed_7370_: usize = 0;
    let mut v_res_7371_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7369_ = lean_unbox_usize(v_sz_7360_);
    lean_dec(v_sz_7360_);
    v_i_boxed_7370_ = lean_unbox_usize(v_i_7361_);
    lean_dec(v_i_7361_);
    v_res_7371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_7359_, v_sz_boxed_7369_, v_i_boxed_7370_, v_bs_7362_, v___y_7363_, v___y_7364_, v___y_7365_, v___y_7366_, v___y_7367_);
    lean_dec(v___y_7367_);
    lean_dec_ref(v___y_7366_);
    lean_dec(v___y_7365_);
    lean_dec_ref(v___y_7364_);
    lean_dec_ref(v___y_7363_);
    return v_res_7371_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(
    mut v_00_u03b1_7372_: *mut LeanObject,
    mut v_x_7373_: *mut LeanObject,
    mut v_isExporting_7374_: u8,
    mut v___y_7375_: *mut LeanObject,
    mut v___y_7376_: *mut LeanObject,
    mut v___y_7377_: *mut LeanObject,
    mut v___y_7378_: *mut LeanObject,
    mut v___y_7379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    v___x_7381_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_7373_, v_isExporting_7374_, v___y_7375_, v___y_7376_, v___y_7377_, v___y_7378_, v___y_7379_);
    return v___x_7381_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(
    mut v_00_u03b1_7382_: *mut LeanObject,
    mut v_x_7383_: *mut LeanObject,
    mut v_isExporting_7384_: *mut LeanObject,
    mut v___y_7385_: *mut LeanObject,
    mut v___y_7386_: *mut LeanObject,
    mut v___y_7387_: *mut LeanObject,
    mut v___y_7388_: *mut LeanObject,
    mut v___y_7389_: *mut LeanObject,
    mut v___y_7390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_7391_: u8 = 0;
    let mut v_res_7392_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_7391_ = (lean_unbox(v_isExporting_7384_) as u8);
    v_res_7392_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_7382_, v_x_7383_, v_isExporting_boxed_7391_, v___y_7385_, v___y_7386_, v___y_7387_, v___y_7388_, v___y_7389_);
    lean_dec(v___y_7389_);
    lean_dec_ref(v___y_7388_);
    lean_dec(v___y_7387_);
    lean_dec_ref(v___y_7386_);
    lean_dec_ref(v___y_7385_);
    return v_res_7392_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(
    mut v_00_u03b1_7393_: *mut LeanObject,
    mut v_x_7394_: *mut LeanObject,
    mut v_when_7395_: u8,
    mut v___y_7396_: *mut LeanObject,
    mut v___y_7397_: *mut LeanObject,
    mut v___y_7398_: *mut LeanObject,
    mut v___y_7399_: *mut LeanObject,
    mut v___y_7400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    v___x_7402_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_7394_, v_when_7395_, v___y_7396_, v___y_7397_, v___y_7398_, v___y_7399_, v___y_7400_);
    return v___x_7402_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(
    mut v_00_u03b1_7403_: *mut LeanObject,
    mut v_x_7404_: *mut LeanObject,
    mut v_when_7405_: *mut LeanObject,
    mut v___y_7406_: *mut LeanObject,
    mut v___y_7407_: *mut LeanObject,
    mut v___y_7408_: *mut LeanObject,
    mut v___y_7409_: *mut LeanObject,
    mut v___y_7410_: *mut LeanObject,
    mut v___y_7411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_7412_: u8 = 0;
    let mut v_res_7413_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_7412_ = (lean_unbox(v_when_7405_) as u8);
    v_res_7413_ =
        l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(
            v_00_u03b1_7403_,
            v_x_7404_,
            v_when_boxed_7412_,
            v___y_7406_,
            v___y_7407_,
            v___y_7408_,
            v___y_7409_,
            v___y_7410_,
        );
    lean_dec(v___y_7410_);
    lean_dec_ref(v___y_7409_);
    lean_dec(v___y_7408_);
    lean_dec_ref(v___y_7407_);
    lean_dec_ref(v___y_7406_);
    return v_res_7413_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(
    mut v_lparams_7414_: *mut LeanObject,
    mut v_params_7415_: *mut LeanObject,
    mut v_compFields_7416_: *mut LeanObject,
    mut v_levelParams_7417_: *mut LeanObject,
    mut v_as_7418_: *mut LeanObject,
    mut v_as_x27_7419_: *mut LeanObject,
    mut v_b_7420_: *mut LeanObject,
    mut v_a_7421_: *mut LeanObject,
    mut v___y_7422_: *mut LeanObject,
    mut v___y_7423_: *mut LeanObject,
    mut v___y_7424_: *mut LeanObject,
    mut v___y_7425_: *mut LeanObject,
    mut v___y_7426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    v___x_7428_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_7414_, v_params_7415_, v_compFields_7416_, v_levelParams_7417_, v_as_x27_7419_, v_b_7420_, v___y_7422_, v___y_7423_, v___y_7424_, v___y_7425_, v___y_7426_);
    return v___x_7428_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(
    mut v_lparams_7429_: *mut LeanObject,
    mut v_params_7430_: *mut LeanObject,
    mut v_compFields_7431_: *mut LeanObject,
    mut v_levelParams_7432_: *mut LeanObject,
    mut v_as_7433_: *mut LeanObject,
    mut v_as_x27_7434_: *mut LeanObject,
    mut v_b_7435_: *mut LeanObject,
    mut v_a_7436_: *mut LeanObject,
    mut v___y_7437_: *mut LeanObject,
    mut v___y_7438_: *mut LeanObject,
    mut v___y_7439_: *mut LeanObject,
    mut v___y_7440_: *mut LeanObject,
    mut v___y_7441_: *mut LeanObject,
    mut v___y_7442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7443_: *mut LeanObject = core::ptr::null_mut();
    v_res_7443_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(
            v_lparams_7429_,
            v_params_7430_,
            v_compFields_7431_,
            v_levelParams_7432_,
            v_as_7433_,
            v_as_x27_7434_,
            v_b_7435_,
            v_a_7436_,
            v___y_7437_,
            v___y_7438_,
            v___y_7439_,
            v___y_7440_,
            v___y_7441_,
        );
    lean_dec(v___y_7441_);
    lean_dec_ref(v___y_7440_);
    lean_dec(v___y_7439_);
    lean_dec_ref(v___y_7438_);
    lean_dec_ref(v___y_7437_);
    lean_dec(v_as_x27_7434_);
    lean_dec(v_as_7433_);
    return v_res_7443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(
    mut v_v_7444_: *mut LeanObject,
    mut v_compFieldVars_7445_: *mut LeanObject,
    mut v___x_7446_: *mut LeanObject,
    mut v___x_7447_: u8,
    mut v_params_7448_: *mut LeanObject,
    mut v___x_7449_: *mut LeanObject,
    mut v_a_7450_: *mut LeanObject,
    mut v___x_7451_: u8,
    mut v_fields_7452_: *mut LeanObject,
    mut v_x_7453_: *mut LeanObject,
    mut v___y_7454_: *mut LeanObject,
    mut v___y_7455_: *mut LeanObject,
    mut v___y_7456_: *mut LeanObject,
    mut v___y_7457_: *mut LeanObject,
    mut v___y_7458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: u8 = 0;
    let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: u8 = 0;
    let mut v___x_7465_: u8 = 0;
    let mut v___x_7466_: u8 = 0;
    let mut v___x_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: u8 = 0;
    let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7477_: u8 = 0;
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7460_ =
                    l_Lean_Elab_ComputedFields_isScalarField(v_v_7444_, v___y_7457_, v___y_7458_);
                if lean_obj_tag(v___x_7460_) == 0 {
                    v_a_7461_ = lean_ctor_get(v___x_7460_, 0);
                    lean_inc(v_a_7461_);
                    lean_dec_ref_known(v___x_7460_, 1);
                    v___x_7462_ = (lean_unbox(v_a_7461_) as u8);
                    if v___x_7462_ == 0 {
                        lean_dec(v_a_7450_);
                        lean_dec_ref(v___x_7449_);
                        lean_dec_ref(v_params_7448_);
                        v___x_7463_ =
                            l_Array_append___redArg(v_compFieldVars_7445_, v_fields_7452_);
                        v___x_7464_ = 1;
                        v___x_7465_ = (lean_unbox(v_a_7461_) as u8);
                        v___x_7466_ = (lean_unbox(v_a_7461_) as u8);
                        lean_dec(v_a_7461_);
                        v___x_7467_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_7463_,
                            v___x_7446_,
                            v___x_7465_,
                            v___x_7447_,
                            v___x_7466_,
                            v___x_7447_,
                            v___x_7464_,
                            v___y_7455_,
                            v___y_7456_,
                            v___y_7457_,
                            v___y_7458_,
                        );
                        lean_dec_ref(v___x_7463_);
                        return v___x_7467_;
                    } else {
                        lean_dec(v_a_7461_);
                        lean_dec_ref(v___x_7446_);
                        lean_dec_ref(v_compFieldVars_7445_);
                        v___x_7468_ = l_Array_append___redArg(v_params_7448_, v_fields_7452_);
                        v___x_7469_ = l_Lean_mkAppN(v___x_7449_, v___x_7468_);
                        lean_dec_ref(v___x_7468_);
                        v___x_7470_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(
                            v_a_7450_,
                            v___x_7469_,
                            v___y_7455_,
                            v___y_7456_,
                            v___y_7457_,
                            v___y_7458_,
                        );
                        if lean_obj_tag(v___x_7470_) == 0 {
                            v_a_7471_ = lean_ctor_get(v___x_7470_, 0);
                            lean_inc(v_a_7471_);
                            lean_dec_ref_known(v___x_7470_, 1);
                            v___x_7472_ = 1;
                            v___x_7473_ = l_Lean_Meta_mkLambdaFVars(
                                v_fields_7452_,
                                v_a_7471_,
                                v___x_7451_,
                                v___x_7447_,
                                v___x_7451_,
                                v___x_7447_,
                                v___x_7472_,
                                v___y_7455_,
                                v___y_7456_,
                                v___y_7457_,
                                v___y_7458_,
                            );
                            return v___x_7473_;
                        } else {
                            return v___x_7470_;
                        }
                    }
                } else {
                    lean_dec(v_a_7450_);
                    lean_dec_ref(v___x_7449_);
                    lean_dec_ref(v_params_7448_);
                    lean_dec_ref(v___x_7446_);
                    lean_dec_ref(v_compFieldVars_7445_);
                    v_a_7474_ = lean_ctor_get(v___x_7460_, 0);
                    v_isSharedCheck_7481_ = (!lean_is_exclusive(v___x_7460_)) as u8;
                    if v_isSharedCheck_7481_ == 0 {
                        v___x_7476_ = v___x_7460_;
                        v_isShared_7477_ = v_isSharedCheck_7481_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7474_);
                        lean_dec(v___x_7460_);
                        v___x_7476_ = lean_box(0);
                        v_isShared_7477_ = v_isSharedCheck_7481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7477_ == 0 {
                    v___x_7479_ = v___x_7476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7480_, 0, v_a_7474_);
                    v___x_7479_ = v_reuseFailAlloc_7480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(
    mut v_v_7482_: *mut LeanObject,
    mut v_compFieldVars_7483_: *mut LeanObject,
    mut v___x_7484_: *mut LeanObject,
    mut v___x_7485_: *mut LeanObject,
    mut v_params_7486_: *mut LeanObject,
    mut v___x_7487_: *mut LeanObject,
    mut v_a_7488_: *mut LeanObject,
    mut v___x_7489_: *mut LeanObject,
    mut v_fields_7490_: *mut LeanObject,
    mut v_x_7491_: *mut LeanObject,
    mut v___y_7492_: *mut LeanObject,
    mut v___y_7493_: *mut LeanObject,
    mut v___y_7494_: *mut LeanObject,
    mut v___y_7495_: *mut LeanObject,
    mut v___y_7496_: *mut LeanObject,
    mut v___y_7497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14620__boxed_7498_: u8 = 0;
    let mut v___x_14623__boxed_7499_: u8 = 0;
    let mut v_res_7500_: *mut LeanObject = core::ptr::null_mut();
    v___x_14620__boxed_7498_ = (lean_unbox(v___x_7485_) as u8);
    v___x_14623__boxed_7499_ = (lean_unbox(v___x_7489_) as u8);
    v_res_7500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_7482_, v_compFieldVars_7483_, v___x_7484_, v___x_14620__boxed_7498_, v_params_7486_, v___x_7487_, v_a_7488_, v___x_14623__boxed_7499_, v_fields_7490_, v_x_7491_, v___y_7492_, v___y_7493_, v___y_7494_, v___y_7495_, v___y_7496_);
    lean_dec(v___y_7496_);
    lean_dec_ref(v___y_7495_);
    lean_dec(v___y_7494_);
    lean_dec_ref(v___y_7493_);
    lean_dec_ref(v___y_7492_);
    lean_dec_ref(v_x_7491_);
    lean_dec_ref(v_fields_7490_);
    return v_res_7500_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(
    mut v_lparams_7501_: *mut LeanObject,
    mut v_compFieldVars_7502_: *mut LeanObject,
    mut v___x_7503_: *mut LeanObject,
    mut v_params_7504_: *mut LeanObject,
    mut v_a_7505_: *mut LeanObject,
    mut v___x_7506_: u8,
    mut v_sz_7507_: usize,
    mut v_i_7508_: usize,
    mut v_bs_7509_: *mut LeanObject,
    mut v___y_7510_: *mut LeanObject,
    mut v___y_7511_: *mut LeanObject,
    mut v___y_7512_: *mut LeanObject,
    mut v___y_7513_: *mut LeanObject,
    mut v___y_7514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7516_: u8 = 0;
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: usize = 0;
    let mut v___x_7525_: usize = 0;
    let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7531_: u8 = 0;
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7535_: u8 = 0;
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7516_ = lean_usize_dec_lt(v_i_7508_, v_sz_7507_);
                if v___x_7516_ == 0 {
                    lean_dec(v_a_7505_);
                    lean_dec_ref(v_params_7504_);
                    lean_dec_ref(v___x_7503_);
                    lean_dec_ref(v_compFieldVars_7502_);
                    lean_dec(v_lparams_7501_);
                    v___x_7517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7517_, 0, v_bs_7509_);
                    return v___x_7517_;
                } else {
                    v_v_7518_ = lean_array_uget(v_bs_7509_, v_i_7508_);
                    v___x_7519_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7520_ = lean_array_uset(v_bs_7509_, v_i_7508_, v___x_7519_);
                    lean_inc(v_lparams_7501_);
                    lean_inc(v_v_7518_);
                    v___x_7536_ = l_Lean_mkConst(v_v_7518_, v_lparams_7501_);
                    lean_inc_ref(v___x_7536_);
                    v___x_7537_ = l_Lean_mkAppN(v___x_7536_, v_params_7504_);
                    lean_inc(v___y_7514_);
                    lean_inc_ref(v___y_7513_);
                    lean_inc(v___y_7512_);
                    lean_inc_ref(v___y_7511_);
                    v___x_7538_ = lean_infer_type(
                        v___x_7537_,
                        v___y_7511_,
                        v___y_7512_,
                        v___y_7513_,
                        v___y_7514_,
                    );
                    if lean_obj_tag(v___x_7538_) == 0 {
                        v_a_7539_ = lean_ctor_get(v___x_7538_, 0);
                        lean_inc(v_a_7539_);
                        lean_dec_ref_known(v___x_7538_, 1);
                        v___x_7540_ = lean_box((v___x_7516_) as usize);
                        v___x_7541_ = lean_box((v___x_7506_) as usize);
                        lean_inc(v_a_7505_);
                        lean_inc_ref(v_params_7504_);
                        lean_inc_ref(v___x_7503_);
                        lean_inc_ref(v_compFieldVars_7502_);
                        v___f_7542_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed as *mut core::ffi::c_void, 16, 8);
                        lean_closure_set(v___f_7542_, 0, v_v_7518_);
                        lean_closure_set(v___f_7542_, 1, v_compFieldVars_7502_);
                        lean_closure_set(v___f_7542_, 2, v___x_7503_);
                        lean_closure_set(v___f_7542_, 3, v___x_7540_);
                        lean_closure_set(v___f_7542_, 4, v_params_7504_);
                        lean_closure_set(v___f_7542_, 5, v___x_7536_);
                        lean_closure_set(v___f_7542_, 6, v_a_7505_);
                        lean_closure_set(v___f_7542_, 7, v___x_7541_);
                        v___x_7543_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_7539_, v___f_7542_, v___x_7506_, v___y_7510_, v___y_7511_, v___y_7512_, v___y_7513_, v___y_7514_);
                        v___y_7522_ = v___x_7543_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_7536_);
                        lean_dec(v_v_7518_);
                        v___y_7522_ = v___x_7538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_7522_) == 0 {
                    v_a_7523_ = lean_ctor_get(v___y_7522_, 0);
                    lean_inc(v_a_7523_);
                    lean_dec_ref_known(v___y_7522_, 1);
                    v___x_7524_ = 1usize;
                    v___x_7525_ = lean_usize_add(v_i_7508_, v___x_7524_);
                    v___x_7526_ = lean_array_uset(v_bs_x27_7520_, v_i_7508_, v_a_7523_);
                    v_i_7508_ = v___x_7525_;
                    v_bs_7509_ = v___x_7526_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_bs_x27_7520_);
                    lean_dec(v_a_7505_);
                    lean_dec_ref(v_params_7504_);
                    lean_dec_ref(v___x_7503_);
                    lean_dec_ref(v_compFieldVars_7502_);
                    lean_dec(v_lparams_7501_);
                    v_a_7528_ = lean_ctor_get(v___y_7522_, 0);
                    v_isSharedCheck_7535_ = (!lean_is_exclusive(v___y_7522_)) as u8;
                    if v_isSharedCheck_7535_ == 0 {
                        v___x_7530_ = v___y_7522_;
                        v_isShared_7531_ = v_isSharedCheck_7535_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7528_);
                        lean_dec(v___y_7522_);
                        v___x_7530_ = lean_box(0);
                        v_isShared_7531_ = v_isSharedCheck_7535_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7531_ == 0 {
                    v___x_7533_ = v___x_7530_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7534_, 0, v_a_7528_);
                    v___x_7533_ = v_reuseFailAlloc_7534_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(
    mut v_lparams_7544_: *mut LeanObject,
    mut v_compFieldVars_7545_: *mut LeanObject,
    mut v___x_7546_: *mut LeanObject,
    mut v_params_7547_: *mut LeanObject,
    mut v_a_7548_: *mut LeanObject,
    mut v___x_7549_: *mut LeanObject,
    mut v_sz_7550_: *mut LeanObject,
    mut v_i_7551_: *mut LeanObject,
    mut v_bs_7552_: *mut LeanObject,
    mut v___y_7553_: *mut LeanObject,
    mut v___y_7554_: *mut LeanObject,
    mut v___y_7555_: *mut LeanObject,
    mut v___y_7556_: *mut LeanObject,
    mut v___y_7557_: *mut LeanObject,
    mut v___y_7558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14706__boxed_7559_: u8 = 0;
    let mut v_sz_boxed_7560_: usize = 0;
    let mut v_i_boxed_7561_: usize = 0;
    let mut v_res_7562_: *mut LeanObject = core::ptr::null_mut();
    v___x_14706__boxed_7559_ = (lean_unbox(v___x_7549_) as u8);
    v_sz_boxed_7560_ = lean_unbox_usize(v_sz_7550_);
    lean_dec(v_sz_7550_);
    v_i_boxed_7561_ = lean_unbox_usize(v_i_7551_);
    lean_dec(v_i_7551_);
    v_res_7562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_7544_, v_compFieldVars_7545_, v___x_7546_, v_params_7547_, v_a_7548_, v___x_14706__boxed_7559_, v_sz_boxed_7560_, v_i_boxed_7561_, v_bs_7552_, v___y_7553_, v___y_7554_, v___y_7555_, v___y_7556_, v___y_7557_);
    lean_dec(v___y_7557_);
    lean_dec_ref(v___y_7556_);
    lean_dec(v___y_7555_);
    lean_dec_ref(v___y_7554_);
    lean_dec_ref(v___y_7553_);
    return v_res_7562_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(
    mut v_sz_7563_: usize,
    mut v_i_7564_: usize,
    mut v_bs_7565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7566_: u8 = 0;
    let mut v_v_7567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: usize = 0;
    let mut v___x_7572_: usize = 0;
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7566_ = lean_usize_dec_lt(v_i_7564_, v_sz_7563_);
                if v___x_7566_ == 0 {
                    return v_bs_7565_;
                } else {
                    v_v_7567_ = lean_array_uget(v_bs_7565_, v_i_7564_);
                    v___x_7568_ = lean_unsigned_to_nat(0);
                    v_bs_x27_7569_ = lean_array_uset(v_bs_7565_, v_i_7564_, v___x_7568_);
                    v___x_7570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7570_, 0, v_v_7567_);
                    v___x_7571_ = 1usize;
                    v___x_7572_ = lean_usize_add(v_i_7564_, v___x_7571_);
                    v___x_7573_ = lean_array_uset(v_bs_x27_7569_, v_i_7564_, v___x_7570_);
                    v_i_7564_ = v___x_7572_;
                    v_bs_7565_ = v___x_7573_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(
    mut v_sz_7575_: *mut LeanObject,
    mut v_i_7576_: *mut LeanObject,
    mut v_bs_7577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7578_: usize = 0;
    let mut v_i_boxed_7579_: usize = 0;
    let mut v_res_7580_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7578_ = lean_unbox_usize(v_sz_7575_);
    lean_dec(v_sz_7575_);
    v_i_boxed_7579_ = lean_unbox_usize(v_i_7576_);
    lean_dec(v_i_7576_);
    v_res_7580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_7578_, v_i_boxed_7579_, v_bs_7577_);
    return v_res_7580_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(
    mut v_ctors_7583_: *mut LeanObject,
    mut v_lparams_7584_: *mut LeanObject,
    mut v_compFieldVars_7585_: *mut LeanObject,
    mut v_params_7586_: *mut LeanObject,
    mut v_val_7587_: *mut LeanObject,
    mut v___x_7588_: *mut LeanObject,
    mut v_indices_7589_: *mut LeanObject,
    mut v_xImpl_7590_: *mut LeanObject,
    mut v___x_7591_: *mut LeanObject,
    mut v_levelParams_7592_: *mut LeanObject,
    mut v_as_7593_: *mut LeanObject,
    mut v_sz_7594_: usize,
    mut v_i_7595_: usize,
    mut v_b_7596_: *mut LeanObject,
    mut v___y_7597_: *mut LeanObject,
    mut v___y_7598_: *mut LeanObject,
    mut v___y_7599_: *mut LeanObject,
    mut v___y_7600_: *mut LeanObject,
    mut v___y_7601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: usize = 0;
    let mut v___x_7606_: usize = 0;
    let mut v___x_7608_: u8 = 0;
    let mut v___x_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: u8 = 0;
    let mut v___x_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7617_: u8 = 0;
    let mut v___x_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7626_: u8 = 0;
    let mut v___x_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7628_: usize = 0;
    let mut v___x_7629_: usize = 0;
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: u8 = 0;
    let mut v___x_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7660_: usize = 0;
    let mut v___x_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7678_: u8 = 0;
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7682_: u8 = 0;
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: u8 = 0;
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: u8 = 0;
    let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7700_: u8 = 0;
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7704_: u8 = 0;
    let mut v_a_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7708_: u8 = 0;
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7712_: u8 = 0;
    let mut v_a_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7716_: u8 = 0;
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7720_: u8 = 0;
    let mut v_a_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7724_: u8 = 0;
    let mut v___x_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7728_: u8 = 0;
    let mut v_a_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7732_: u8 = 0;
    let mut v___x_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7736_: u8 = 0;
    let mut v_a_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7740_: u8 = 0;
    let mut v___x_7742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7744_: u8 = 0;
    let mut v_a_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7748_: u8 = 0;
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7752_: u8 = 0;
    let mut v_a_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7756_: u8 = 0;
    let mut v___x_7758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7760_: u8 = 0;
    let mut v_a_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v_a_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7772_: u8 = 0;
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7776_: u8 = 0;
    let mut v_a_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7784_: u8 = 0;
    let mut v___x_7785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7791_: u8 = 0;
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7795_: u8 = 0;
    let mut v_reuseFailAlloc_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7797_: u8 = 0;
    let mut v_unused_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7608_ = lean_usize_dec_lt(v_i_7595_, v_sz_7594_);
                if v___x_7608_ == 0 {
                    lean_dec(v_levelParams_7592_);
                    lean_dec(v___x_7591_);
                    lean_dec_ref(v_xImpl_7590_);
                    lean_dec_ref(v_indices_7589_);
                    lean_dec_ref(v___x_7588_);
                    lean_dec_ref(v_val_7587_);
                    lean_dec_ref(v_params_7586_);
                    lean_dec_ref(v_compFieldVars_7585_);
                    lean_dec(v_lparams_7584_);
                    lean_dec(v_ctors_7583_);
                    v___x_7609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7609_, 0, v_b_7596_);
                    return v___x_7609_;
                } else {
                    v_array_7610_ = lean_ctor_get(v_b_7596_, 0);
                    v_start_7611_ = lean_ctor_get(v_b_7596_, 1);
                    v_stop_7612_ = lean_ctor_get(v_b_7596_, 2);
                    v___x_7613_ = lean_nat_dec_lt(v_start_7611_, v_stop_7612_);
                    if v___x_7613_ == 0 {
                        lean_dec(v_levelParams_7592_);
                        lean_dec(v___x_7591_);
                        lean_dec_ref(v_xImpl_7590_);
                        lean_dec_ref(v_indices_7589_);
                        lean_dec_ref(v___x_7588_);
                        lean_dec_ref(v_val_7587_);
                        lean_dec_ref(v_params_7586_);
                        lean_dec_ref(v_compFieldVars_7585_);
                        lean_dec(v_lparams_7584_);
                        lean_dec(v_ctors_7583_);
                        v___x_7614_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7614_, 0, v_b_7596_);
                        return v___x_7614_;
                    } else {
                        lean_inc(v_stop_7612_);
                        lean_inc(v_start_7611_);
                        lean_inc_ref(v_array_7610_);
                        v_isSharedCheck_7797_ = (!lean_is_exclusive(v_b_7596_)) as u8;
                        if v_isSharedCheck_7797_ == 0 {
                            v_unused_7798_ = lean_ctor_get(v_b_7596_, 2);
                            lean_dec(v_unused_7798_);
                            v_unused_7799_ = lean_ctor_get(v_b_7596_, 1);
                            lean_dec(v_unused_7799_);
                            v_unused_7800_ = lean_ctor_get(v_b_7596_, 0);
                            lean_dec(v_unused_7800_);
                            v___x_7616_ = v_b_7596_;
                            v_isShared_7617_ = v_isSharedCheck_7797_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_b_7596_);
                            v___x_7616_ = lean_box(0);
                            v_isShared_7617_ = v_isSharedCheck_7797_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7605_ = 1usize;
                v___x_7606_ = lean_usize_add(v_i_7595_, v___x_7605_);
                v_i_7595_ = v___x_7606_;
                v_b_7596_ = v_a_7604_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7618_ = lean_st_ref_get(v___y_7601_);
                v_env_7619_ = lean_ctor_get(v___x_7618_, 0);
                lean_inc_ref(v_env_7619_);
                lean_dec(v___x_7618_);
                v___x_7620_ = lean_array_fget(v_array_7610_, v_start_7611_);
                v_a_7621_ = lean_array_uget_borrowed(v_as_7593_, v_i_7595_);
                v___x_7622_ = lean_unsigned_to_nat(1);
                v___x_7623_ = lean_nat_add(v_start_7611_, v___x_7622_);
                lean_dec(v_start_7611_);
                if v_isShared_7617_ == 0 {
                    lean_ctor_set(v___x_7616_, 1, v___x_7623_);
                    v___x_7625_ = v___x_7616_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7796_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7796_, 0, v_array_7610_);
                    lean_ctor_set(v_reuseFailAlloc_7796_, 1, v___x_7623_);
                    lean_ctor_set(v_reuseFailAlloc_7796_, 2, v_stop_7612_);
                    v___x_7625_ = v_reuseFailAlloc_7796_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_a_7621_);
                v___x_7626_ = l_Lean_isExtern(v_env_7619_, v_a_7621_);
                if v___x_7626_ == 0 {
                    lean_inc(v_ctors_7583_);
                    v___x_7627_ = lean_array_mk(v_ctors_7583_);
                    v_sz_7628_ = lean_array_size(v___x_7627_);
                    v___x_7629_ = 0usize;
                    v___x_7630_ = lean_box((v___x_7626_) as usize);
                    v___x_7631_ = lean_box_usize(v_sz_7628_);
                    v___x_7632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1;
                    lean_inc(v_a_7621_);
                    lean_inc_ref(v_params_7586_);
                    lean_inc(v___x_7620_);
                    lean_inc_ref(v_compFieldVars_7585_);
                    lean_inc(v_lparams_7584_);
                    v___x_7633_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed as *mut core::ffi::c_void, 15, 9);
                    lean_closure_set(v___x_7633_, 0, v_lparams_7584_);
                    lean_closure_set(v___x_7633_, 1, v_compFieldVars_7585_);
                    lean_closure_set(v___x_7633_, 2, v___x_7620_);
                    lean_closure_set(v___x_7633_, 3, v_params_7586_);
                    lean_closure_set(v___x_7633_, 4, v_a_7621_);
                    lean_closure_set(v___x_7633_, 5, v___x_7630_);
                    lean_closure_set(v___x_7633_, 6, v___x_7631_);
                    lean_closure_set(v___x_7633_, 7, v___x_7632_);
                    lean_closure_set(v___x_7633_, 8, v___x_7627_);
                    v___x_7634_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_7633_, v___x_7613_, v___y_7597_, v___y_7598_, v___y_7599_, v___y_7600_, v___y_7601_);
                    if lean_obj_tag(v___x_7634_) == 0 {
                        v_a_7635_ = lean_ctor_get(v___x_7634_, 0);
                        lean_inc(v_a_7635_);
                        lean_dec_ref_known(v___x_7634_, 1);
                        lean_inc(v___y_7601_);
                        lean_inc_ref(v___y_7600_);
                        lean_inc(v___y_7599_);
                        lean_inc_ref(v___y_7598_);
                        lean_inc(v___x_7620_);
                        v___x_7636_ = lean_infer_type(
                            v___x_7620_,
                            v___y_7598_,
                            v___y_7599_,
                            v___y_7600_,
                            v___y_7601_,
                        );
                        if lean_obj_tag(v___x_7636_) == 0 {
                            v_a_7637_ = lean_ctor_get(v___x_7636_, 0);
                            lean_inc(v_a_7637_);
                            lean_dec_ref_known(v___x_7636_, 1);
                            v___x_7638_ = lean_mk_empty_array_with_capacity(v___x_7622_);
                            lean_inc_ref(v_val_7587_);
                            lean_inc_ref(v___x_7638_);
                            v___x_7639_ = lean_array_push(v___x_7638_, v_val_7587_);
                            lean_inc_ref(v___x_7588_);
                            v___x_7640_ = l_Array_append___redArg(v___x_7588_, v___x_7639_);
                            lean_dec_ref(v___x_7639_);
                            v___x_7641_ = 1;
                            v___x_7642_ = l_Lean_Meta_mkForallFVars(
                                v___x_7640_,
                                v_a_7637_,
                                v___x_7626_,
                                v___x_7613_,
                                v___x_7613_,
                                v___x_7641_,
                                v___y_7598_,
                                v___y_7599_,
                                v___y_7600_,
                                v___y_7601_,
                            );
                            if lean_obj_tag(v___x_7642_) == 0 {
                                v_a_7643_ = lean_ctor_get(v___x_7642_, 0);
                                lean_inc(v_a_7643_);
                                lean_dec_ref_known(v___x_7642_, 1);
                                lean_inc(v___y_7601_);
                                lean_inc_ref(v___y_7600_);
                                lean_inc(v___y_7599_);
                                lean_inc_ref(v___y_7598_);
                                v___x_7644_ = lean_infer_type(
                                    v___x_7620_,
                                    v___y_7598_,
                                    v___y_7599_,
                                    v___y_7600_,
                                    v___y_7601_,
                                );
                                if lean_obj_tag(v___x_7644_) == 0 {
                                    v_a_7645_ = lean_ctor_get(v___x_7644_, 0);
                                    lean_inc(v_a_7645_);
                                    lean_dec_ref_known(v___x_7644_, 1);
                                    lean_inc_ref(v_xImpl_7590_);
                                    lean_inc_ref(v_indices_7589_);
                                    v___x_7646_ = lean_array_push(v_indices_7589_, v_xImpl_7590_);
                                    v___x_7647_ = l_Lean_Meta_mkLambdaFVars(
                                        v___x_7646_,
                                        v_a_7645_,
                                        v___x_7626_,
                                        v___x_7613_,
                                        v___x_7626_,
                                        v___x_7613_,
                                        v___x_7641_,
                                        v___y_7598_,
                                        v___y_7599_,
                                        v___y_7600_,
                                        v___y_7601_,
                                    );
                                    lean_dec_ref(v___x_7646_);
                                    if lean_obj_tag(v___x_7647_) == 0 {
                                        v_a_7648_ = lean_ctor_get(v___x_7647_, 0);
                                        lean_inc(v_a_7648_);
                                        lean_dec_ref_known(v___x_7647_, 1);
                                        lean_inc(v___y_7601_);
                                        lean_inc_ref(v___y_7600_);
                                        lean_inc(v___y_7599_);
                                        lean_inc_ref(v___y_7598_);
                                        lean_inc_ref(v_xImpl_7590_);
                                        v___x_7649_ = lean_infer_type(
                                            v_xImpl_7590_,
                                            v___y_7598_,
                                            v___y_7599_,
                                            v___y_7600_,
                                            v___y_7601_,
                                        );
                                        if lean_obj_tag(v___x_7649_) == 0 {
                                            v_a_7650_ = lean_ctor_get(v___x_7649_, 0);
                                            lean_inc(v_a_7650_);
                                            lean_dec_ref_known(v___x_7649_, 1);
                                            lean_inc_ref(v_val_7587_);
                                            v___x_7651_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
                                                v_a_7650_,
                                                v_val_7587_,
                                                v___y_7598_,
                                                v___y_7599_,
                                                v___y_7600_,
                                                v___y_7601_,
                                            );
                                            if lean_obj_tag(v___x_7651_) == 0 {
                                                v_a_7652_ = lean_ctor_get(v___x_7651_, 0);
                                                lean_inc(v_a_7652_);
                                                lean_dec_ref_known(v___x_7651_, 1);
                                                lean_inc(v___x_7591_);
                                                v___x_7653_ = l_Lean_mkCasesOnName(v___x_7591_);
                                                lean_inc_ref(v___x_7638_);
                                                v___x_7654_ =
                                                    lean_array_push(v___x_7638_, v_a_7648_);
                                                lean_inc_ref(v_params_7586_);
                                                v___x_7655_ = l_Array_append___redArg(
                                                    v_params_7586_,
                                                    v___x_7654_,
                                                );
                                                lean_dec_ref(v___x_7654_);
                                                v___x_7656_ = l_Array_append___redArg(
                                                    v___x_7655_,
                                                    v_indices_7589_,
                                                );
                                                v___x_7657_ =
                                                    lean_array_push(v___x_7638_, v_a_7652_);
                                                v___x_7658_ = l_Array_append___redArg(
                                                    v___x_7656_,
                                                    v___x_7657_,
                                                );
                                                lean_dec_ref(v___x_7657_);
                                                v___x_7659_ =
                                                    l_Array_append___redArg(v___x_7658_, v_a_7635_);
                                                lean_dec(v_a_7635_);
                                                v_sz_7660_ = lean_array_size(v___x_7659_);
                                                v___x_7661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_7660_, v___x_7629_, v___x_7659_);
                                                v___x_7662_ = l_Lean_Meta_mkAppOptM(
                                                    v___x_7653_,
                                                    v___x_7661_,
                                                    v___y_7598_,
                                                    v___y_7599_,
                                                    v___y_7600_,
                                                    v___y_7601_,
                                                );
                                                if lean_obj_tag(v___x_7662_) == 0 {
                                                    v_a_7663_ = lean_ctor_get(v___x_7662_, 0);
                                                    lean_inc(v_a_7663_);
                                                    lean_dec_ref_known(v___x_7662_, 1);
                                                    v___x_7664_ = l_Lean_Meta_mkLambdaFVars(
                                                        v___x_7640_,
                                                        v_a_7663_,
                                                        v___x_7626_,
                                                        v___x_7613_,
                                                        v___x_7626_,
                                                        v___x_7613_,
                                                        v___x_7641_,
                                                        v___y_7598_,
                                                        v___y_7599_,
                                                        v___y_7600_,
                                                        v___y_7601_,
                                                    );
                                                    lean_dec_ref(v___x_7640_);
                                                    if lean_obj_tag(v___x_7664_) == 0 {
                                                        v_a_7665_ = lean_ctor_get(v___x_7664_, 0);
                                                        lean_inc(v_a_7665_);
                                                        lean_dec_ref_known(v___x_7664_, 1);
                                                        v___x_7666_ = l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                                                        lean_inc(v_a_7621_);
                                                        v___x_7667_ = l_Lean_Name_append(
                                                            v_a_7621_,
                                                            v___x_7666_,
                                                        );
                                                        lean_inc(v_levelParams_7592_);
                                                        lean_inc_n(v___x_7667_, 2);
                                                        v___x_7683_ =
                                                            lean_alloc_ctor(0, 3, (0) as u32);
                                                        lean_ctor_set(v___x_7683_, 0, v___x_7667_);
                                                        lean_ctor_set(
                                                            v___x_7683_,
                                                            1,
                                                            v_levelParams_7592_,
                                                        );
                                                        lean_ctor_set(v___x_7683_, 2, v_a_7643_);
                                                        v___x_7684_ = lean_box(0);
                                                        v___x_7685_ = 0;
                                                        v___x_7686_ = lean_box(0);
                                                        v___x_7687_ =
                                                            lean_alloc_ctor(1, 2, (0) as u32);
                                                        lean_ctor_set(v___x_7687_, 0, v___x_7667_);
                                                        lean_ctor_set(v___x_7687_, 1, v___x_7686_);
                                                        v___x_7688_ =
                                                            lean_alloc_ctor(0, 4, (1) as u32);
                                                        lean_ctor_set(v___x_7688_, 0, v___x_7683_);
                                                        lean_ctor_set(v___x_7688_, 1, v_a_7665_);
                                                        lean_ctor_set(v___x_7688_, 2, v___x_7684_);
                                                        lean_ctor_set(v___x_7688_, 3, v___x_7687_);
                                                        lean_ctor_set_uint8(
                                                            v___x_7688_,
                                                            (core::mem::size_of::<*mut LeanObject>(
                                                            ) * 4)
                                                                as u32,
                                                            v___x_7685_,
                                                        );
                                                        v___x_7689_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(v___x_7689_, 0, v___x_7688_);
                                                        v___x_7690_ = l_Lean_addDecl(
                                                            v___x_7689_,
                                                            v___x_7626_,
                                                            v___y_7600_,
                                                            v___y_7601_,
                                                        );
                                                        if lean_obj_tag(v___x_7690_) == 0 {
                                                            lean_dec_ref_known(v___x_7690_, 1);
                                                            v___x_7691_ =
                                                                lean_st_ref_get(v___y_7601_);
                                                            v_env_7692_ =
                                                                lean_ctor_get(v___x_7691_, 0);
                                                            lean_inc_ref(v_env_7692_);
                                                            lean_dec(v___x_7691_);
                                                            lean_inc(v_a_7621_);
                                                            v___x_7693_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_7692_, v_a_7621_);
                                                            if lean_obj_tag(v___x_7693_) == 1 {
                                                                v_val_7694_ =
                                                                    lean_ctor_get(v___x_7693_, 0);
                                                                lean_inc(v_val_7694_);
                                                                lean_dec_ref_known(v___x_7693_, 1);
                                                                v___x_7695_ =
                                                                    (lean_unbox(v_val_7694_) as u8);
                                                                lean_dec(v_val_7694_);
                                                                lean_inc(v___x_7667_);
                                                                v___x_7696_ =
                                                                    l_Lean_Meta_setInlineAttribute(
                                                                        v___x_7667_,
                                                                        v___x_7695_,
                                                                        v___y_7598_,
                                                                        v___y_7599_,
                                                                        v___y_7600_,
                                                                        v___y_7601_,
                                                                    );
                                                                if lean_obj_tag(v___x_7696_) == 0 {
                                                                    lean_dec_ref_known(
                                                                        v___x_7696_,
                                                                        1,
                                                                    );
                                                                    v___y_7669_ = v___y_7597_;
                                                                    v___y_7670_ = v___y_7598_;
                                                                    v___y_7671_ = v___y_7599_;
                                                                    v___y_7672_ = v___y_7600_;
                                                                    v___y_7673_ = v___y_7601_;
                                                                    state = 4;
                                                                    continue;
                                                                } else {
                                                                    lean_dec(v___x_7667_);
                                                                    lean_dec_ref(v___x_7625_);
                                                                    lean_dec(v_levelParams_7592_);
                                                                    lean_dec(v___x_7591_);
                                                                    lean_dec_ref(v_xImpl_7590_);
                                                                    lean_dec_ref(v_indices_7589_);
                                                                    lean_dec_ref(v___x_7588_);
                                                                    lean_dec_ref(v_val_7587_);
                                                                    lean_dec_ref(v_params_7586_);
                                                                    lean_dec_ref(
                                                                        v_compFieldVars_7585_,
                                                                    );
                                                                    lean_dec(v_lparams_7584_);
                                                                    lean_dec(v_ctors_7583_);
                                                                    v_a_7697_ = lean_ctor_get(
                                                                        v___x_7696_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_7704_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_7696_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_7704_ == 0 {
                                                                        v___x_7699_ = v___x_7696_;
                                                                        v_isShared_7700_ =
                                                                            v_isSharedCheck_7704_;
                                                                        state = 7;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_7697_);
                                                                        lean_dec(v___x_7696_);
                                                                        v___x_7699_ = lean_box(0);
                                                                        v_isShared_7700_ =
                                                                            v_isSharedCheck_7704_;
                                                                        state = 7;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec(v___x_7693_);
                                                                v___y_7669_ = v___y_7597_;
                                                                v___y_7670_ = v___y_7598_;
                                                                v___y_7671_ = v___y_7599_;
                                                                v___y_7672_ = v___y_7600_;
                                                                v___y_7673_ = v___y_7601_;
                                                                state = 4;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v___x_7667_);
                                                            lean_dec_ref(v___x_7625_);
                                                            lean_dec(v_levelParams_7592_);
                                                            lean_dec(v___x_7591_);
                                                            lean_dec_ref(v_xImpl_7590_);
                                                            lean_dec_ref(v_indices_7589_);
                                                            lean_dec_ref(v___x_7588_);
                                                            lean_dec_ref(v_val_7587_);
                                                            lean_dec_ref(v_params_7586_);
                                                            lean_dec_ref(v_compFieldVars_7585_);
                                                            lean_dec(v_lparams_7584_);
                                                            lean_dec(v_ctors_7583_);
                                                            v_a_7705_ =
                                                                lean_ctor_get(v___x_7690_, 0);
                                                            v_isSharedCheck_7712_ =
                                                                (!lean_is_exclusive(v___x_7690_))
                                                                    as u8;
                                                            if v_isSharedCheck_7712_ == 0 {
                                                                v___x_7707_ = v___x_7690_;
                                                                v_isShared_7708_ =
                                                                    v_isSharedCheck_7712_;
                                                                state = 9;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_7705_);
                                                                lean_dec(v___x_7690_);
                                                                v___x_7707_ = lean_box(0);
                                                                v_isShared_7708_ =
                                                                    v_isSharedCheck_7712_;
                                                                state = 9;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_7643_);
                                                        lean_dec_ref(v___x_7625_);
                                                        lean_dec(v_levelParams_7592_);
                                                        lean_dec(v___x_7591_);
                                                        lean_dec_ref(v_xImpl_7590_);
                                                        lean_dec_ref(v_indices_7589_);
                                                        lean_dec_ref(v___x_7588_);
                                                        lean_dec_ref(v_val_7587_);
                                                        lean_dec_ref(v_params_7586_);
                                                        lean_dec_ref(v_compFieldVars_7585_);
                                                        lean_dec(v_lparams_7584_);
                                                        lean_dec(v_ctors_7583_);
                                                        v_a_7713_ = lean_ctor_get(v___x_7664_, 0);
                                                        v_isSharedCheck_7720_ =
                                                            (!lean_is_exclusive(v___x_7664_)) as u8;
                                                        if v_isSharedCheck_7720_ == 0 {
                                                            v___x_7715_ = v___x_7664_;
                                                            v_isShared_7716_ =
                                                                v_isSharedCheck_7720_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_7713_);
                                                            lean_dec(v___x_7664_);
                                                            v___x_7715_ = lean_box(0);
                                                            v_isShared_7716_ =
                                                                v_isSharedCheck_7720_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_a_7643_);
                                                    lean_dec_ref(v___x_7640_);
                                                    lean_dec_ref(v___x_7625_);
                                                    lean_dec(v_levelParams_7592_);
                                                    lean_dec(v___x_7591_);
                                                    lean_dec_ref(v_xImpl_7590_);
                                                    lean_dec_ref(v_indices_7589_);
                                                    lean_dec_ref(v___x_7588_);
                                                    lean_dec_ref(v_val_7587_);
                                                    lean_dec_ref(v_params_7586_);
                                                    lean_dec_ref(v_compFieldVars_7585_);
                                                    lean_dec(v_lparams_7584_);
                                                    lean_dec(v_ctors_7583_);
                                                    v_a_7721_ = lean_ctor_get(v___x_7662_, 0);
                                                    v_isSharedCheck_7728_ =
                                                        (!lean_is_exclusive(v___x_7662_)) as u8;
                                                    if v_isSharedCheck_7728_ == 0 {
                                                        v___x_7723_ = v___x_7662_;
                                                        v_isShared_7724_ = v_isSharedCheck_7728_;
                                                        state = 13;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7721_);
                                                        lean_dec(v___x_7662_);
                                                        v___x_7723_ = lean_box(0);
                                                        v_isShared_7724_ = v_isSharedCheck_7728_;
                                                        state = 13;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_7648_);
                                                lean_dec(v_a_7643_);
                                                lean_dec_ref(v___x_7640_);
                                                lean_dec_ref(v___x_7638_);
                                                lean_dec(v_a_7635_);
                                                lean_dec_ref(v___x_7625_);
                                                lean_dec(v_levelParams_7592_);
                                                lean_dec(v___x_7591_);
                                                lean_dec_ref(v_xImpl_7590_);
                                                lean_dec_ref(v_indices_7589_);
                                                lean_dec_ref(v___x_7588_);
                                                lean_dec_ref(v_val_7587_);
                                                lean_dec_ref(v_params_7586_);
                                                lean_dec_ref(v_compFieldVars_7585_);
                                                lean_dec(v_lparams_7584_);
                                                lean_dec(v_ctors_7583_);
                                                v_a_7729_ = lean_ctor_get(v___x_7651_, 0);
                                                v_isSharedCheck_7736_ =
                                                    (!lean_is_exclusive(v___x_7651_)) as u8;
                                                if v_isSharedCheck_7736_ == 0 {
                                                    v___x_7731_ = v___x_7651_;
                                                    v_isShared_7732_ = v_isSharedCheck_7736_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7729_);
                                                    lean_dec(v___x_7651_);
                                                    v___x_7731_ = lean_box(0);
                                                    v_isShared_7732_ = v_isSharedCheck_7736_;
                                                    state = 15;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_7648_);
                                            lean_dec(v_a_7643_);
                                            lean_dec_ref(v___x_7640_);
                                            lean_dec_ref(v___x_7638_);
                                            lean_dec(v_a_7635_);
                                            lean_dec_ref(v___x_7625_);
                                            lean_dec(v_levelParams_7592_);
                                            lean_dec(v___x_7591_);
                                            lean_dec_ref(v_xImpl_7590_);
                                            lean_dec_ref(v_indices_7589_);
                                            lean_dec_ref(v___x_7588_);
                                            lean_dec_ref(v_val_7587_);
                                            lean_dec_ref(v_params_7586_);
                                            lean_dec_ref(v_compFieldVars_7585_);
                                            lean_dec(v_lparams_7584_);
                                            lean_dec(v_ctors_7583_);
                                            v_a_7737_ = lean_ctor_get(v___x_7649_, 0);
                                            v_isSharedCheck_7744_ =
                                                (!lean_is_exclusive(v___x_7649_)) as u8;
                                            if v_isSharedCheck_7744_ == 0 {
                                                v___x_7739_ = v___x_7649_;
                                                v_isShared_7740_ = v_isSharedCheck_7744_;
                                                state = 17;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7737_);
                                                lean_dec(v___x_7649_);
                                                v___x_7739_ = lean_box(0);
                                                v_isShared_7740_ = v_isSharedCheck_7744_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_7643_);
                                        lean_dec_ref(v___x_7640_);
                                        lean_dec_ref(v___x_7638_);
                                        lean_dec(v_a_7635_);
                                        lean_dec_ref(v___x_7625_);
                                        lean_dec(v_levelParams_7592_);
                                        lean_dec(v___x_7591_);
                                        lean_dec_ref(v_xImpl_7590_);
                                        lean_dec_ref(v_indices_7589_);
                                        lean_dec_ref(v___x_7588_);
                                        lean_dec_ref(v_val_7587_);
                                        lean_dec_ref(v_params_7586_);
                                        lean_dec_ref(v_compFieldVars_7585_);
                                        lean_dec(v_lparams_7584_);
                                        lean_dec(v_ctors_7583_);
                                        v_a_7745_ = lean_ctor_get(v___x_7647_, 0);
                                        v_isSharedCheck_7752_ =
                                            (!lean_is_exclusive(v___x_7647_)) as u8;
                                        if v_isSharedCheck_7752_ == 0 {
                                            v___x_7747_ = v___x_7647_;
                                            v_isShared_7748_ = v_isSharedCheck_7752_;
                                            state = 19;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7745_);
                                            lean_dec(v___x_7647_);
                                            v___x_7747_ = lean_box(0);
                                            v_isShared_7748_ = v_isSharedCheck_7752_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_7643_);
                                    lean_dec_ref(v___x_7640_);
                                    lean_dec_ref(v___x_7638_);
                                    lean_dec(v_a_7635_);
                                    lean_dec_ref(v___x_7625_);
                                    lean_dec(v_levelParams_7592_);
                                    lean_dec(v___x_7591_);
                                    lean_dec_ref(v_xImpl_7590_);
                                    lean_dec_ref(v_indices_7589_);
                                    lean_dec_ref(v___x_7588_);
                                    lean_dec_ref(v_val_7587_);
                                    lean_dec_ref(v_params_7586_);
                                    lean_dec_ref(v_compFieldVars_7585_);
                                    lean_dec(v_lparams_7584_);
                                    lean_dec(v_ctors_7583_);
                                    v_a_7753_ = lean_ctor_get(v___x_7644_, 0);
                                    v_isSharedCheck_7760_ = (!lean_is_exclusive(v___x_7644_)) as u8;
                                    if v_isSharedCheck_7760_ == 0 {
                                        v___x_7755_ = v___x_7644_;
                                        v_isShared_7756_ = v_isSharedCheck_7760_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7753_);
                                        lean_dec(v___x_7644_);
                                        v___x_7755_ = lean_box(0);
                                        v_isShared_7756_ = v_isSharedCheck_7760_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_7640_);
                                lean_dec_ref(v___x_7638_);
                                lean_dec(v_a_7635_);
                                lean_dec_ref(v___x_7625_);
                                lean_dec(v___x_7620_);
                                lean_dec(v_levelParams_7592_);
                                lean_dec(v___x_7591_);
                                lean_dec_ref(v_xImpl_7590_);
                                lean_dec_ref(v_indices_7589_);
                                lean_dec_ref(v___x_7588_);
                                lean_dec_ref(v_val_7587_);
                                lean_dec_ref(v_params_7586_);
                                lean_dec_ref(v_compFieldVars_7585_);
                                lean_dec(v_lparams_7584_);
                                lean_dec(v_ctors_7583_);
                                v_a_7761_ = lean_ctor_get(v___x_7642_, 0);
                                v_isSharedCheck_7768_ = (!lean_is_exclusive(v___x_7642_)) as u8;
                                if v_isSharedCheck_7768_ == 0 {
                                    v___x_7763_ = v___x_7642_;
                                    v_isShared_7764_ = v_isSharedCheck_7768_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_a_7761_);
                                    lean_dec(v___x_7642_);
                                    v___x_7763_ = lean_box(0);
                                    v_isShared_7764_ = v_isSharedCheck_7768_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7635_);
                            lean_dec_ref(v___x_7625_);
                            lean_dec(v___x_7620_);
                            lean_dec(v_levelParams_7592_);
                            lean_dec(v___x_7591_);
                            lean_dec_ref(v_xImpl_7590_);
                            lean_dec_ref(v_indices_7589_);
                            lean_dec_ref(v___x_7588_);
                            lean_dec_ref(v_val_7587_);
                            lean_dec_ref(v_params_7586_);
                            lean_dec_ref(v_compFieldVars_7585_);
                            lean_dec(v_lparams_7584_);
                            lean_dec(v_ctors_7583_);
                            v_a_7769_ = lean_ctor_get(v___x_7636_, 0);
                            v_isSharedCheck_7776_ = (!lean_is_exclusive(v___x_7636_)) as u8;
                            if v_isSharedCheck_7776_ == 0 {
                                v___x_7771_ = v___x_7636_;
                                v_isShared_7772_ = v_isSharedCheck_7776_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_7769_);
                                lean_dec(v___x_7636_);
                                v___x_7771_ = lean_box(0);
                                v_isShared_7772_ = v_isSharedCheck_7776_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_7625_);
                        lean_dec(v___x_7620_);
                        lean_dec(v_levelParams_7592_);
                        lean_dec(v___x_7591_);
                        lean_dec_ref(v_xImpl_7590_);
                        lean_dec_ref(v_indices_7589_);
                        lean_dec_ref(v___x_7588_);
                        lean_dec_ref(v_val_7587_);
                        lean_dec_ref(v_params_7586_);
                        lean_dec_ref(v_compFieldVars_7585_);
                        lean_dec(v_lparams_7584_);
                        lean_dec(v_ctors_7583_);
                        v_a_7777_ = lean_ctor_get(v___x_7634_, 0);
                        v_isSharedCheck_7784_ = (!lean_is_exclusive(v___x_7634_)) as u8;
                        if v_isSharedCheck_7784_ == 0 {
                            v___x_7779_ = v___x_7634_;
                            v_isShared_7780_ = v_isSharedCheck_7784_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_7777_);
                            lean_dec(v___x_7634_);
                            v___x_7779_ = lean_box(0);
                            v_isShared_7780_ = v_isSharedCheck_7784_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7620_);
                    v___x_7785_ = lean_mk_empty_array_with_capacity(v___x_7622_);
                    lean_inc(v_a_7621_);
                    v___x_7786_ = lean_array_push(v___x_7785_, v_a_7621_);
                    v___x_7787_ =
                        l_Lean_compileDecls(v___x_7786_, v___x_7613_, v___y_7600_, v___y_7601_);
                    if lean_obj_tag(v___x_7787_) == 0 {
                        lean_dec_ref_known(v___x_7787_, 1);
                        v_a_7604_ = v___x_7625_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_7625_);
                        lean_dec(v_levelParams_7592_);
                        lean_dec(v___x_7591_);
                        lean_dec_ref(v_xImpl_7590_);
                        lean_dec_ref(v_indices_7589_);
                        lean_dec_ref(v___x_7588_);
                        lean_dec_ref(v_val_7587_);
                        lean_dec_ref(v_params_7586_);
                        lean_dec_ref(v_compFieldVars_7585_);
                        lean_dec(v_lparams_7584_);
                        lean_dec(v_ctors_7583_);
                        v_a_7788_ = lean_ctor_get(v___x_7787_, 0);
                        v_isSharedCheck_7795_ = (!lean_is_exclusive(v___x_7787_)) as u8;
                        if v_isSharedCheck_7795_ == 0 {
                            v___x_7790_ = v___x_7787_;
                            v_isShared_7791_ = v_isSharedCheck_7795_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_7788_);
                            lean_dec(v___x_7787_);
                            v___x_7790_ = lean_box(0);
                            v_isShared_7791_ = v_isSharedCheck_7795_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            4 => {
                lean_inc(v_a_7621_);
                v___x_7674_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_7621_, v___x_7667_, v___y_7669_, v___y_7670_, v___y_7671_, v___y_7672_, v___y_7673_);
                if lean_obj_tag(v___x_7674_) == 0 {
                    lean_dec_ref_known(v___x_7674_, 1);
                    v_a_7604_ = v___x_7625_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_7625_);
                    lean_dec(v_levelParams_7592_);
                    lean_dec(v___x_7591_);
                    lean_dec_ref(v_xImpl_7590_);
                    lean_dec_ref(v_indices_7589_);
                    lean_dec_ref(v___x_7588_);
                    lean_dec_ref(v_val_7587_);
                    lean_dec_ref(v_params_7586_);
                    lean_dec_ref(v_compFieldVars_7585_);
                    lean_dec(v_lparams_7584_);
                    lean_dec(v_ctors_7583_);
                    v_a_7675_ = lean_ctor_get(v___x_7674_, 0);
                    v_isSharedCheck_7682_ = (!lean_is_exclusive(v___x_7674_)) as u8;
                    if v_isSharedCheck_7682_ == 0 {
                        v___x_7677_ = v___x_7674_;
                        v_isShared_7678_ = v_isSharedCheck_7682_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7675_);
                        lean_dec(v___x_7674_);
                        v___x_7677_ = lean_box(0);
                        v_isShared_7678_ = v_isSharedCheck_7682_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_7678_ == 0 {
                    v___x_7680_ = v___x_7677_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7681_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7681_, 0, v_a_7675_);
                    v___x_7680_ = v_reuseFailAlloc_7681_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7680_;
            }
            7 => {
                if v_isShared_7700_ == 0 {
                    v___x_7702_ = v___x_7699_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7703_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7703_, 0, v_a_7697_);
                    v___x_7702_ = v_reuseFailAlloc_7703_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7702_;
            }
            9 => {
                if v_isShared_7708_ == 0 {
                    v___x_7710_ = v___x_7707_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7711_, 0, v_a_7705_);
                    v___x_7710_ = v_reuseFailAlloc_7711_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7710_;
            }
            11 => {
                if v_isShared_7716_ == 0 {
                    v___x_7718_ = v___x_7715_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7719_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7719_, 0, v_a_7713_);
                    v___x_7718_ = v_reuseFailAlloc_7719_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7718_;
            }
            13 => {
                if v_isShared_7724_ == 0 {
                    v___x_7726_ = v___x_7723_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7727_, 0, v_a_7721_);
                    v___x_7726_ = v_reuseFailAlloc_7727_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7726_;
            }
            15 => {
                if v_isShared_7732_ == 0 {
                    v___x_7734_ = v___x_7731_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7735_, 0, v_a_7729_);
                    v___x_7734_ = v_reuseFailAlloc_7735_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7734_;
            }
            17 => {
                if v_isShared_7740_ == 0 {
                    v___x_7742_ = v___x_7739_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7743_, 0, v_a_7737_);
                    v___x_7742_ = v_reuseFailAlloc_7743_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7742_;
            }
            19 => {
                if v_isShared_7748_ == 0 {
                    v___x_7750_ = v___x_7747_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7751_, 0, v_a_7745_);
                    v___x_7750_ = v_reuseFailAlloc_7751_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7750_;
            }
            21 => {
                if v_isShared_7756_ == 0 {
                    v___x_7758_ = v___x_7755_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7759_, 0, v_a_7753_);
                    v___x_7758_ = v_reuseFailAlloc_7759_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7758_;
            }
            23 => {
                if v_isShared_7764_ == 0 {
                    v___x_7766_ = v___x_7763_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
                    v___x_7766_ = v_reuseFailAlloc_7767_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7766_;
            }
            25 => {
                if v_isShared_7772_ == 0 {
                    v___x_7774_ = v___x_7771_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7775_, 0, v_a_7769_);
                    v___x_7774_ = v_reuseFailAlloc_7775_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_7774_;
            }
            27 => {
                if v_isShared_7780_ == 0 {
                    v___x_7782_ = v___x_7779_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7783_, 0, v_a_7777_);
                    v___x_7782_ = v_reuseFailAlloc_7783_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_7782_;
            }
            29 => {
                if v_isShared_7791_ == 0 {
                    v___x_7793_ = v___x_7790_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_7794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7794_, 0, v_a_7788_);
                    v___x_7793_ = v_reuseFailAlloc_7794_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_7793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctors_7801_: *mut LeanObject = *_args.add(0);
    let mut v_lparams_7802_: *mut LeanObject = *_args.add(1);
    let mut v_compFieldVars_7803_: *mut LeanObject = *_args.add(2);
    let mut v_params_7804_: *mut LeanObject = *_args.add(3);
    let mut v_val_7805_: *mut LeanObject = *_args.add(4);
    let mut v___x_7806_: *mut LeanObject = *_args.add(5);
    let mut v_indices_7807_: *mut LeanObject = *_args.add(6);
    let mut v_xImpl_7808_: *mut LeanObject = *_args.add(7);
    let mut v___x_7809_: *mut LeanObject = *_args.add(8);
    let mut v_levelParams_7810_: *mut LeanObject = *_args.add(9);
    let mut v_as_7811_: *mut LeanObject = *_args.add(10);
    let mut v_sz_7812_: *mut LeanObject = *_args.add(11);
    let mut v_i_7813_: *mut LeanObject = *_args.add(12);
    let mut v_b_7814_: *mut LeanObject = *_args.add(13);
    let mut v___y_7815_: *mut LeanObject = *_args.add(14);
    let mut v___y_7816_: *mut LeanObject = *_args.add(15);
    let mut v___y_7817_: *mut LeanObject = *_args.add(16);
    let mut v___y_7818_: *mut LeanObject = *_args.add(17);
    let mut v___y_7819_: *mut LeanObject = *_args.add(18);
    let mut v___y_7820_: *mut LeanObject = *_args.add(19);
    let mut v_sz_boxed_7821_: usize = 0;
    let mut v_i_boxed_7822_: usize = 0;
    let mut v_res_7823_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7821_ = lean_unbox_usize(v_sz_7812_);
    lean_dec(v_sz_7812_);
    v_i_boxed_7822_ = lean_unbox_usize(v_i_7813_);
    lean_dec(v_i_7813_);
    v_res_7823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_7801_, v_lparams_7802_, v_compFieldVars_7803_, v_params_7804_, v_val_7805_, v___x_7806_, v_indices_7807_, v_xImpl_7808_, v___x_7809_, v_levelParams_7810_, v_as_7811_, v_sz_boxed_7821_, v_i_boxed_7822_, v_b_7814_, v___y_7815_, v___y_7816_, v___y_7817_, v___y_7818_, v___y_7819_);
    lean_dec(v___y_7819_);
    lean_dec_ref(v___y_7818_);
    lean_dec(v___y_7817_);
    lean_dec_ref(v___y_7816_);
    lean_dec_ref(v___y_7815_);
    lean_dec_ref(v_as_7811_);
    return v_res_7823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(
    mut v_lparams_7824_: *mut LeanObject,
    mut v_compFieldVars_7825_: *mut LeanObject,
    mut v_params_7826_: *mut LeanObject,
    mut v_ctors_7827_: *mut LeanObject,
    mut v_val_7828_: *mut LeanObject,
    mut v___x_7829_: *mut LeanObject,
    mut v_indices_7830_: *mut LeanObject,
    mut v_xImpl_7831_: *mut LeanObject,
    mut v___x_7832_: *mut LeanObject,
    mut v_levelParams_7833_: *mut LeanObject,
    mut v_as_7834_: *mut LeanObject,
    mut v_sz_7835_: usize,
    mut v_i_7836_: usize,
    mut v_b_7837_: *mut LeanObject,
    mut v___y_7838_: *mut LeanObject,
    mut v___y_7839_: *mut LeanObject,
    mut v___y_7840_: *mut LeanObject,
    mut v___y_7841_: *mut LeanObject,
    mut v___y_7842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: usize = 0;
    let mut v___x_7847_: usize = 0;
    let mut v___x_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7849_: u8 = 0;
    let mut v___x_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: u8 = 0;
    let mut v___x_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7858_: u8 = 0;
    let mut v___x_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: u8 = 0;
    let mut v___x_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7869_: usize = 0;
    let mut v___x_7870_: usize = 0;
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: u8 = 0;
    let mut v___x_7883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7901_: usize = 0;
    let mut v___x_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7919_: u8 = 0;
    let mut v___x_7921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7923_: u8 = 0;
    let mut v___x_7924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: u8 = 0;
    let mut v___x_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: u8 = 0;
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7941_: u8 = 0;
    let mut v___x_7943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7945_: u8 = 0;
    let mut v_a_7946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7949_: u8 = 0;
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7953_: u8 = 0;
    let mut v_a_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7957_: u8 = 0;
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7961_: u8 = 0;
    let mut v_a_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7965_: u8 = 0;
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7969_: u8 = 0;
    let mut v_a_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7973_: u8 = 0;
    let mut v___x_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7977_: u8 = 0;
    let mut v_a_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7981_: u8 = 0;
    let mut v___x_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7985_: u8 = 0;
    let mut v_a_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7989_: u8 = 0;
    let mut v___x_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7993_: u8 = 0;
    let mut v_a_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7997_: u8 = 0;
    let mut v___x_7999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8001_: u8 = 0;
    let mut v_a_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8005_: u8 = 0;
    let mut v___x_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8009_: u8 = 0;
    let mut v_a_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8013_: u8 = 0;
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8017_: u8 = 0;
    let mut v_a_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8021_: u8 = 0;
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8025_: u8 = 0;
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8032_: u8 = 0;
    let mut v___x_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8036_: u8 = 0;
    let mut v_reuseFailAlloc_8037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8038_: u8 = 0;
    let mut v_unused_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7849_ = lean_usize_dec_lt(v_i_7836_, v_sz_7835_);
                if v___x_7849_ == 0 {
                    lean_dec(v_levelParams_7833_);
                    lean_dec(v___x_7832_);
                    lean_dec_ref(v_xImpl_7831_);
                    lean_dec_ref(v_indices_7830_);
                    lean_dec_ref(v___x_7829_);
                    lean_dec_ref(v_val_7828_);
                    lean_dec(v_ctors_7827_);
                    lean_dec_ref(v_params_7826_);
                    lean_dec_ref(v_compFieldVars_7825_);
                    lean_dec(v_lparams_7824_);
                    v___x_7850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7850_, 0, v_b_7837_);
                    return v___x_7850_;
                } else {
                    v_array_7851_ = lean_ctor_get(v_b_7837_, 0);
                    v_start_7852_ = lean_ctor_get(v_b_7837_, 1);
                    v_stop_7853_ = lean_ctor_get(v_b_7837_, 2);
                    v___x_7854_ = lean_nat_dec_lt(v_start_7852_, v_stop_7853_);
                    if v___x_7854_ == 0 {
                        lean_dec(v_levelParams_7833_);
                        lean_dec(v___x_7832_);
                        lean_dec_ref(v_xImpl_7831_);
                        lean_dec_ref(v_indices_7830_);
                        lean_dec_ref(v___x_7829_);
                        lean_dec_ref(v_val_7828_);
                        lean_dec(v_ctors_7827_);
                        lean_dec_ref(v_params_7826_);
                        lean_dec_ref(v_compFieldVars_7825_);
                        lean_dec(v_lparams_7824_);
                        v___x_7855_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7855_, 0, v_b_7837_);
                        return v___x_7855_;
                    } else {
                        lean_inc(v_stop_7853_);
                        lean_inc(v_start_7852_);
                        lean_inc_ref(v_array_7851_);
                        v_isSharedCheck_8038_ = (!lean_is_exclusive(v_b_7837_)) as u8;
                        if v_isSharedCheck_8038_ == 0 {
                            v_unused_8039_ = lean_ctor_get(v_b_7837_, 2);
                            lean_dec(v_unused_8039_);
                            v_unused_8040_ = lean_ctor_get(v_b_7837_, 1);
                            lean_dec(v_unused_8040_);
                            v_unused_8041_ = lean_ctor_get(v_b_7837_, 0);
                            lean_dec(v_unused_8041_);
                            v___x_7857_ = v_b_7837_;
                            v_isShared_7858_ = v_isSharedCheck_8038_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_b_7837_);
                            v___x_7857_ = lean_box(0);
                            v_isShared_7858_ = v_isSharedCheck_8038_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7846_ = 1usize;
                v___x_7847_ = lean_usize_add(v_i_7836_, v___x_7846_);
                v___x_7848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_7827_, v_lparams_7824_, v_compFieldVars_7825_, v_params_7826_, v_val_7828_, v___x_7829_, v_indices_7830_, v_xImpl_7831_, v___x_7832_, v_levelParams_7833_, v_as_7834_, v_sz_7835_, v___x_7847_, v_a_7845_, v___y_7838_, v___y_7839_, v___y_7840_, v___y_7841_, v___y_7842_);
                return v___x_7848_;
            }
            2 => {
                v___x_7859_ = lean_st_ref_get(v___y_7842_);
                v_env_7860_ = lean_ctor_get(v___x_7859_, 0);
                lean_inc_ref(v_env_7860_);
                lean_dec(v___x_7859_);
                v___x_7861_ = lean_array_fget(v_array_7851_, v_start_7852_);
                v_a_7862_ = lean_array_uget_borrowed(v_as_7834_, v_i_7836_);
                v___x_7863_ = lean_unsigned_to_nat(1);
                v___x_7864_ = lean_nat_add(v_start_7852_, v___x_7863_);
                lean_dec(v_start_7852_);
                if v_isShared_7858_ == 0 {
                    lean_ctor_set(v___x_7857_, 1, v___x_7864_);
                    v___x_7866_ = v___x_7857_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8037_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8037_, 0, v_array_7851_);
                    lean_ctor_set(v_reuseFailAlloc_8037_, 1, v___x_7864_);
                    lean_ctor_set(v_reuseFailAlloc_8037_, 2, v_stop_7853_);
                    v___x_7866_ = v_reuseFailAlloc_8037_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_a_7862_);
                v___x_7867_ = l_Lean_isExtern(v_env_7860_, v_a_7862_);
                if v___x_7867_ == 0 {
                    lean_inc(v_ctors_7827_);
                    v___x_7868_ = lean_array_mk(v_ctors_7827_);
                    v_sz_7869_ = lean_array_size(v___x_7868_);
                    v___x_7870_ = 0usize;
                    v___x_7871_ = lean_box((v___x_7867_) as usize);
                    v___x_7872_ = lean_box_usize(v_sz_7869_);
                    v___x_7873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1;
                    lean_inc(v_a_7862_);
                    lean_inc_ref(v_params_7826_);
                    lean_inc(v___x_7861_);
                    lean_inc_ref(v_compFieldVars_7825_);
                    lean_inc(v_lparams_7824_);
                    v___x_7874_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed as *mut core::ffi::c_void, 15, 9);
                    lean_closure_set(v___x_7874_, 0, v_lparams_7824_);
                    lean_closure_set(v___x_7874_, 1, v_compFieldVars_7825_);
                    lean_closure_set(v___x_7874_, 2, v___x_7861_);
                    lean_closure_set(v___x_7874_, 3, v_params_7826_);
                    lean_closure_set(v___x_7874_, 4, v_a_7862_);
                    lean_closure_set(v___x_7874_, 5, v___x_7871_);
                    lean_closure_set(v___x_7874_, 6, v___x_7872_);
                    lean_closure_set(v___x_7874_, 7, v___x_7873_);
                    lean_closure_set(v___x_7874_, 8, v___x_7868_);
                    v___x_7875_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_7874_, v___x_7854_, v___y_7838_, v___y_7839_, v___y_7840_, v___y_7841_, v___y_7842_);
                    if lean_obj_tag(v___x_7875_) == 0 {
                        v_a_7876_ = lean_ctor_get(v___x_7875_, 0);
                        lean_inc(v_a_7876_);
                        lean_dec_ref_known(v___x_7875_, 1);
                        lean_inc(v___y_7842_);
                        lean_inc_ref(v___y_7841_);
                        lean_inc(v___y_7840_);
                        lean_inc_ref(v___y_7839_);
                        lean_inc(v___x_7861_);
                        v___x_7877_ = lean_infer_type(
                            v___x_7861_,
                            v___y_7839_,
                            v___y_7840_,
                            v___y_7841_,
                            v___y_7842_,
                        );
                        if lean_obj_tag(v___x_7877_) == 0 {
                            v_a_7878_ = lean_ctor_get(v___x_7877_, 0);
                            lean_inc(v_a_7878_);
                            lean_dec_ref_known(v___x_7877_, 1);
                            v___x_7879_ = lean_mk_empty_array_with_capacity(v___x_7863_);
                            lean_inc_ref(v_val_7828_);
                            lean_inc_ref(v___x_7879_);
                            v___x_7880_ = lean_array_push(v___x_7879_, v_val_7828_);
                            lean_inc_ref(v___x_7829_);
                            v___x_7881_ = l_Array_append___redArg(v___x_7829_, v___x_7880_);
                            lean_dec_ref(v___x_7880_);
                            v___x_7882_ = 1;
                            v___x_7883_ = l_Lean_Meta_mkForallFVars(
                                v___x_7881_,
                                v_a_7878_,
                                v___x_7867_,
                                v___x_7854_,
                                v___x_7854_,
                                v___x_7882_,
                                v___y_7839_,
                                v___y_7840_,
                                v___y_7841_,
                                v___y_7842_,
                            );
                            if lean_obj_tag(v___x_7883_) == 0 {
                                v_a_7884_ = lean_ctor_get(v___x_7883_, 0);
                                lean_inc(v_a_7884_);
                                lean_dec_ref_known(v___x_7883_, 1);
                                lean_inc(v___y_7842_);
                                lean_inc_ref(v___y_7841_);
                                lean_inc(v___y_7840_);
                                lean_inc_ref(v___y_7839_);
                                v___x_7885_ = lean_infer_type(
                                    v___x_7861_,
                                    v___y_7839_,
                                    v___y_7840_,
                                    v___y_7841_,
                                    v___y_7842_,
                                );
                                if lean_obj_tag(v___x_7885_) == 0 {
                                    v_a_7886_ = lean_ctor_get(v___x_7885_, 0);
                                    lean_inc(v_a_7886_);
                                    lean_dec_ref_known(v___x_7885_, 1);
                                    lean_inc_ref(v_xImpl_7831_);
                                    lean_inc_ref(v_indices_7830_);
                                    v___x_7887_ = lean_array_push(v_indices_7830_, v_xImpl_7831_);
                                    v___x_7888_ = l_Lean_Meta_mkLambdaFVars(
                                        v___x_7887_,
                                        v_a_7886_,
                                        v___x_7867_,
                                        v___x_7854_,
                                        v___x_7867_,
                                        v___x_7854_,
                                        v___x_7882_,
                                        v___y_7839_,
                                        v___y_7840_,
                                        v___y_7841_,
                                        v___y_7842_,
                                    );
                                    lean_dec_ref(v___x_7887_);
                                    if lean_obj_tag(v___x_7888_) == 0 {
                                        v_a_7889_ = lean_ctor_get(v___x_7888_, 0);
                                        lean_inc(v_a_7889_);
                                        lean_dec_ref_known(v___x_7888_, 1);
                                        lean_inc(v___y_7842_);
                                        lean_inc_ref(v___y_7841_);
                                        lean_inc(v___y_7840_);
                                        lean_inc_ref(v___y_7839_);
                                        lean_inc_ref(v_xImpl_7831_);
                                        v___x_7890_ = lean_infer_type(
                                            v_xImpl_7831_,
                                            v___y_7839_,
                                            v___y_7840_,
                                            v___y_7841_,
                                            v___y_7842_,
                                        );
                                        if lean_obj_tag(v___x_7890_) == 0 {
                                            v_a_7891_ = lean_ctor_get(v___x_7890_, 0);
                                            lean_inc(v_a_7891_);
                                            lean_dec_ref_known(v___x_7890_, 1);
                                            lean_inc_ref(v_val_7828_);
                                            v___x_7892_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(
                                                v_a_7891_,
                                                v_val_7828_,
                                                v___y_7839_,
                                                v___y_7840_,
                                                v___y_7841_,
                                                v___y_7842_,
                                            );
                                            if lean_obj_tag(v___x_7892_) == 0 {
                                                v_a_7893_ = lean_ctor_get(v___x_7892_, 0);
                                                lean_inc(v_a_7893_);
                                                lean_dec_ref_known(v___x_7892_, 1);
                                                lean_inc(v___x_7832_);
                                                v___x_7894_ = l_Lean_mkCasesOnName(v___x_7832_);
                                                lean_inc_ref(v___x_7879_);
                                                v___x_7895_ =
                                                    lean_array_push(v___x_7879_, v_a_7889_);
                                                lean_inc_ref(v_params_7826_);
                                                v___x_7896_ = l_Array_append___redArg(
                                                    v_params_7826_,
                                                    v___x_7895_,
                                                );
                                                lean_dec_ref(v___x_7895_);
                                                v___x_7897_ = l_Array_append___redArg(
                                                    v___x_7896_,
                                                    v_indices_7830_,
                                                );
                                                v___x_7898_ =
                                                    lean_array_push(v___x_7879_, v_a_7893_);
                                                v___x_7899_ = l_Array_append___redArg(
                                                    v___x_7897_,
                                                    v___x_7898_,
                                                );
                                                lean_dec_ref(v___x_7898_);
                                                v___x_7900_ =
                                                    l_Array_append___redArg(v___x_7899_, v_a_7876_);
                                                lean_dec(v_a_7876_);
                                                v_sz_7901_ = lean_array_size(v___x_7900_);
                                                v___x_7902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_7901_, v___x_7870_, v___x_7900_);
                                                v___x_7903_ = l_Lean_Meta_mkAppOptM(
                                                    v___x_7894_,
                                                    v___x_7902_,
                                                    v___y_7839_,
                                                    v___y_7840_,
                                                    v___y_7841_,
                                                    v___y_7842_,
                                                );
                                                if lean_obj_tag(v___x_7903_) == 0 {
                                                    v_a_7904_ = lean_ctor_get(v___x_7903_, 0);
                                                    lean_inc(v_a_7904_);
                                                    lean_dec_ref_known(v___x_7903_, 1);
                                                    v___x_7905_ = l_Lean_Meta_mkLambdaFVars(
                                                        v___x_7881_,
                                                        v_a_7904_,
                                                        v___x_7867_,
                                                        v___x_7854_,
                                                        v___x_7867_,
                                                        v___x_7854_,
                                                        v___x_7882_,
                                                        v___y_7839_,
                                                        v___y_7840_,
                                                        v___y_7841_,
                                                        v___y_7842_,
                                                    );
                                                    lean_dec_ref(v___x_7881_);
                                                    if lean_obj_tag(v___x_7905_) == 0 {
                                                        v_a_7906_ = lean_ctor_get(v___x_7905_, 0);
                                                        lean_inc(v_a_7906_);
                                                        lean_dec_ref_known(v___x_7905_, 1);
                                                        v___x_7907_ = l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                                                        lean_inc(v_a_7862_);
                                                        v___x_7908_ = l_Lean_Name_append(
                                                            v_a_7862_,
                                                            v___x_7907_,
                                                        );
                                                        lean_inc(v_levelParams_7833_);
                                                        lean_inc_n(v___x_7908_, 2);
                                                        v___x_7924_ =
                                                            lean_alloc_ctor(0, 3, (0) as u32);
                                                        lean_ctor_set(v___x_7924_, 0, v___x_7908_);
                                                        lean_ctor_set(
                                                            v___x_7924_,
                                                            1,
                                                            v_levelParams_7833_,
                                                        );
                                                        lean_ctor_set(v___x_7924_, 2, v_a_7884_);
                                                        v___x_7925_ = lean_box(0);
                                                        v___x_7926_ = 0;
                                                        v___x_7927_ = lean_box(0);
                                                        v___x_7928_ =
                                                            lean_alloc_ctor(1, 2, (0) as u32);
                                                        lean_ctor_set(v___x_7928_, 0, v___x_7908_);
                                                        lean_ctor_set(v___x_7928_, 1, v___x_7927_);
                                                        v___x_7929_ =
                                                            lean_alloc_ctor(0, 4, (1) as u32);
                                                        lean_ctor_set(v___x_7929_, 0, v___x_7924_);
                                                        lean_ctor_set(v___x_7929_, 1, v_a_7906_);
                                                        lean_ctor_set(v___x_7929_, 2, v___x_7925_);
                                                        lean_ctor_set(v___x_7929_, 3, v___x_7928_);
                                                        lean_ctor_set_uint8(
                                                            v___x_7929_,
                                                            (core::mem::size_of::<*mut LeanObject>(
                                                            ) * 4)
                                                                as u32,
                                                            v___x_7926_,
                                                        );
                                                        v___x_7930_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(v___x_7930_, 0, v___x_7929_);
                                                        v___x_7931_ = l_Lean_addDecl(
                                                            v___x_7930_,
                                                            v___x_7867_,
                                                            v___y_7841_,
                                                            v___y_7842_,
                                                        );
                                                        if lean_obj_tag(v___x_7931_) == 0 {
                                                            lean_dec_ref_known(v___x_7931_, 1);
                                                            v___x_7932_ =
                                                                lean_st_ref_get(v___y_7842_);
                                                            v_env_7933_ =
                                                                lean_ctor_get(v___x_7932_, 0);
                                                            lean_inc_ref(v_env_7933_);
                                                            lean_dec(v___x_7932_);
                                                            lean_inc(v_a_7862_);
                                                            v___x_7934_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_7933_, v_a_7862_);
                                                            if lean_obj_tag(v___x_7934_) == 1 {
                                                                v_val_7935_ =
                                                                    lean_ctor_get(v___x_7934_, 0);
                                                                lean_inc(v_val_7935_);
                                                                lean_dec_ref_known(v___x_7934_, 1);
                                                                v___x_7936_ =
                                                                    (lean_unbox(v_val_7935_) as u8);
                                                                lean_dec(v_val_7935_);
                                                                lean_inc(v___x_7908_);
                                                                v___x_7937_ =
                                                                    l_Lean_Meta_setInlineAttribute(
                                                                        v___x_7908_,
                                                                        v___x_7936_,
                                                                        v___y_7839_,
                                                                        v___y_7840_,
                                                                        v___y_7841_,
                                                                        v___y_7842_,
                                                                    );
                                                                if lean_obj_tag(v___x_7937_) == 0 {
                                                                    lean_dec_ref_known(
                                                                        v___x_7937_,
                                                                        1,
                                                                    );
                                                                    v___y_7910_ = v___y_7838_;
                                                                    v___y_7911_ = v___y_7839_;
                                                                    v___y_7912_ = v___y_7840_;
                                                                    v___y_7913_ = v___y_7841_;
                                                                    v___y_7914_ = v___y_7842_;
                                                                    state = 4;
                                                                    continue;
                                                                } else {
                                                                    lean_dec(v___x_7908_);
                                                                    lean_dec_ref(v___x_7866_);
                                                                    lean_dec(v_levelParams_7833_);
                                                                    lean_dec(v___x_7832_);
                                                                    lean_dec_ref(v_xImpl_7831_);
                                                                    lean_dec_ref(v_indices_7830_);
                                                                    lean_dec_ref(v___x_7829_);
                                                                    lean_dec_ref(v_val_7828_);
                                                                    lean_dec(v_ctors_7827_);
                                                                    lean_dec_ref(v_params_7826_);
                                                                    lean_dec_ref(
                                                                        v_compFieldVars_7825_,
                                                                    );
                                                                    lean_dec(v_lparams_7824_);
                                                                    v_a_7938_ = lean_ctor_get(
                                                                        v___x_7937_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_7945_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_7937_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_7945_ == 0 {
                                                                        v___x_7940_ = v___x_7937_;
                                                                        v_isShared_7941_ =
                                                                            v_isSharedCheck_7945_;
                                                                        state = 7;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_7938_);
                                                                        lean_dec(v___x_7937_);
                                                                        v___x_7940_ = lean_box(0);
                                                                        v_isShared_7941_ =
                                                                            v_isSharedCheck_7945_;
                                                                        state = 7;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec(v___x_7934_);
                                                                v___y_7910_ = v___y_7838_;
                                                                v___y_7911_ = v___y_7839_;
                                                                v___y_7912_ = v___y_7840_;
                                                                v___y_7913_ = v___y_7841_;
                                                                v___y_7914_ = v___y_7842_;
                                                                state = 4;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v___x_7908_);
                                                            lean_dec_ref(v___x_7866_);
                                                            lean_dec(v_levelParams_7833_);
                                                            lean_dec(v___x_7832_);
                                                            lean_dec_ref(v_xImpl_7831_);
                                                            lean_dec_ref(v_indices_7830_);
                                                            lean_dec_ref(v___x_7829_);
                                                            lean_dec_ref(v_val_7828_);
                                                            lean_dec(v_ctors_7827_);
                                                            lean_dec_ref(v_params_7826_);
                                                            lean_dec_ref(v_compFieldVars_7825_);
                                                            lean_dec(v_lparams_7824_);
                                                            v_a_7946_ =
                                                                lean_ctor_get(v___x_7931_, 0);
                                                            v_isSharedCheck_7953_ =
                                                                (!lean_is_exclusive(v___x_7931_))
                                                                    as u8;
                                                            if v_isSharedCheck_7953_ == 0 {
                                                                v___x_7948_ = v___x_7931_;
                                                                v_isShared_7949_ =
                                                                    v_isSharedCheck_7953_;
                                                                state = 9;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_7946_);
                                                                lean_dec(v___x_7931_);
                                                                v___x_7948_ = lean_box(0);
                                                                v_isShared_7949_ =
                                                                    v_isSharedCheck_7953_;
                                                                state = 9;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_7884_);
                                                        lean_dec_ref(v___x_7866_);
                                                        lean_dec(v_levelParams_7833_);
                                                        lean_dec(v___x_7832_);
                                                        lean_dec_ref(v_xImpl_7831_);
                                                        lean_dec_ref(v_indices_7830_);
                                                        lean_dec_ref(v___x_7829_);
                                                        lean_dec_ref(v_val_7828_);
                                                        lean_dec(v_ctors_7827_);
                                                        lean_dec_ref(v_params_7826_);
                                                        lean_dec_ref(v_compFieldVars_7825_);
                                                        lean_dec(v_lparams_7824_);
                                                        v_a_7954_ = lean_ctor_get(v___x_7905_, 0);
                                                        v_isSharedCheck_7961_ =
                                                            (!lean_is_exclusive(v___x_7905_)) as u8;
                                                        if v_isSharedCheck_7961_ == 0 {
                                                            v___x_7956_ = v___x_7905_;
                                                            v_isShared_7957_ =
                                                                v_isSharedCheck_7961_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_7954_);
                                                            lean_dec(v___x_7905_);
                                                            v___x_7956_ = lean_box(0);
                                                            v_isShared_7957_ =
                                                                v_isSharedCheck_7961_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_a_7884_);
                                                    lean_dec_ref(v___x_7881_);
                                                    lean_dec_ref(v___x_7866_);
                                                    lean_dec(v_levelParams_7833_);
                                                    lean_dec(v___x_7832_);
                                                    lean_dec_ref(v_xImpl_7831_);
                                                    lean_dec_ref(v_indices_7830_);
                                                    lean_dec_ref(v___x_7829_);
                                                    lean_dec_ref(v_val_7828_);
                                                    lean_dec(v_ctors_7827_);
                                                    lean_dec_ref(v_params_7826_);
                                                    lean_dec_ref(v_compFieldVars_7825_);
                                                    lean_dec(v_lparams_7824_);
                                                    v_a_7962_ = lean_ctor_get(v___x_7903_, 0);
                                                    v_isSharedCheck_7969_ =
                                                        (!lean_is_exclusive(v___x_7903_)) as u8;
                                                    if v_isSharedCheck_7969_ == 0 {
                                                        v___x_7964_ = v___x_7903_;
                                                        v_isShared_7965_ = v_isSharedCheck_7969_;
                                                        state = 13;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7962_);
                                                        lean_dec(v___x_7903_);
                                                        v___x_7964_ = lean_box(0);
                                                        v_isShared_7965_ = v_isSharedCheck_7969_;
                                                        state = 13;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_7889_);
                                                lean_dec(v_a_7884_);
                                                lean_dec_ref(v___x_7881_);
                                                lean_dec_ref(v___x_7879_);
                                                lean_dec(v_a_7876_);
                                                lean_dec_ref(v___x_7866_);
                                                lean_dec(v_levelParams_7833_);
                                                lean_dec(v___x_7832_);
                                                lean_dec_ref(v_xImpl_7831_);
                                                lean_dec_ref(v_indices_7830_);
                                                lean_dec_ref(v___x_7829_);
                                                lean_dec_ref(v_val_7828_);
                                                lean_dec(v_ctors_7827_);
                                                lean_dec_ref(v_params_7826_);
                                                lean_dec_ref(v_compFieldVars_7825_);
                                                lean_dec(v_lparams_7824_);
                                                v_a_7970_ = lean_ctor_get(v___x_7892_, 0);
                                                v_isSharedCheck_7977_ =
                                                    (!lean_is_exclusive(v___x_7892_)) as u8;
                                                if v_isSharedCheck_7977_ == 0 {
                                                    v___x_7972_ = v___x_7892_;
                                                    v_isShared_7973_ = v_isSharedCheck_7977_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7970_);
                                                    lean_dec(v___x_7892_);
                                                    v___x_7972_ = lean_box(0);
                                                    v_isShared_7973_ = v_isSharedCheck_7977_;
                                                    state = 15;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_7889_);
                                            lean_dec(v_a_7884_);
                                            lean_dec_ref(v___x_7881_);
                                            lean_dec_ref(v___x_7879_);
                                            lean_dec(v_a_7876_);
                                            lean_dec_ref(v___x_7866_);
                                            lean_dec(v_levelParams_7833_);
                                            lean_dec(v___x_7832_);
                                            lean_dec_ref(v_xImpl_7831_);
                                            lean_dec_ref(v_indices_7830_);
                                            lean_dec_ref(v___x_7829_);
                                            lean_dec_ref(v_val_7828_);
                                            lean_dec(v_ctors_7827_);
                                            lean_dec_ref(v_params_7826_);
                                            lean_dec_ref(v_compFieldVars_7825_);
                                            lean_dec(v_lparams_7824_);
                                            v_a_7978_ = lean_ctor_get(v___x_7890_, 0);
                                            v_isSharedCheck_7985_ =
                                                (!lean_is_exclusive(v___x_7890_)) as u8;
                                            if v_isSharedCheck_7985_ == 0 {
                                                v___x_7980_ = v___x_7890_;
                                                v_isShared_7981_ = v_isSharedCheck_7985_;
                                                state = 17;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7978_);
                                                lean_dec(v___x_7890_);
                                                v___x_7980_ = lean_box(0);
                                                v_isShared_7981_ = v_isSharedCheck_7985_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_7884_);
                                        lean_dec_ref(v___x_7881_);
                                        lean_dec_ref(v___x_7879_);
                                        lean_dec(v_a_7876_);
                                        lean_dec_ref(v___x_7866_);
                                        lean_dec(v_levelParams_7833_);
                                        lean_dec(v___x_7832_);
                                        lean_dec_ref(v_xImpl_7831_);
                                        lean_dec_ref(v_indices_7830_);
                                        lean_dec_ref(v___x_7829_);
                                        lean_dec_ref(v_val_7828_);
                                        lean_dec(v_ctors_7827_);
                                        lean_dec_ref(v_params_7826_);
                                        lean_dec_ref(v_compFieldVars_7825_);
                                        lean_dec(v_lparams_7824_);
                                        v_a_7986_ = lean_ctor_get(v___x_7888_, 0);
                                        v_isSharedCheck_7993_ =
                                            (!lean_is_exclusive(v___x_7888_)) as u8;
                                        if v_isSharedCheck_7993_ == 0 {
                                            v___x_7988_ = v___x_7888_;
                                            v_isShared_7989_ = v_isSharedCheck_7993_;
                                            state = 19;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7986_);
                                            lean_dec(v___x_7888_);
                                            v___x_7988_ = lean_box(0);
                                            v_isShared_7989_ = v_isSharedCheck_7993_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_7884_);
                                    lean_dec_ref(v___x_7881_);
                                    lean_dec_ref(v___x_7879_);
                                    lean_dec(v_a_7876_);
                                    lean_dec_ref(v___x_7866_);
                                    lean_dec(v_levelParams_7833_);
                                    lean_dec(v___x_7832_);
                                    lean_dec_ref(v_xImpl_7831_);
                                    lean_dec_ref(v_indices_7830_);
                                    lean_dec_ref(v___x_7829_);
                                    lean_dec_ref(v_val_7828_);
                                    lean_dec(v_ctors_7827_);
                                    lean_dec_ref(v_params_7826_);
                                    lean_dec_ref(v_compFieldVars_7825_);
                                    lean_dec(v_lparams_7824_);
                                    v_a_7994_ = lean_ctor_get(v___x_7885_, 0);
                                    v_isSharedCheck_8001_ = (!lean_is_exclusive(v___x_7885_)) as u8;
                                    if v_isSharedCheck_8001_ == 0 {
                                        v___x_7996_ = v___x_7885_;
                                        v_isShared_7997_ = v_isSharedCheck_8001_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7994_);
                                        lean_dec(v___x_7885_);
                                        v___x_7996_ = lean_box(0);
                                        v_isShared_7997_ = v_isSharedCheck_8001_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_7881_);
                                lean_dec_ref(v___x_7879_);
                                lean_dec(v_a_7876_);
                                lean_dec_ref(v___x_7866_);
                                lean_dec(v___x_7861_);
                                lean_dec(v_levelParams_7833_);
                                lean_dec(v___x_7832_);
                                lean_dec_ref(v_xImpl_7831_);
                                lean_dec_ref(v_indices_7830_);
                                lean_dec_ref(v___x_7829_);
                                lean_dec_ref(v_val_7828_);
                                lean_dec(v_ctors_7827_);
                                lean_dec_ref(v_params_7826_);
                                lean_dec_ref(v_compFieldVars_7825_);
                                lean_dec(v_lparams_7824_);
                                v_a_8002_ = lean_ctor_get(v___x_7883_, 0);
                                v_isSharedCheck_8009_ = (!lean_is_exclusive(v___x_7883_)) as u8;
                                if v_isSharedCheck_8009_ == 0 {
                                    v___x_8004_ = v___x_7883_;
                                    v_isShared_8005_ = v_isSharedCheck_8009_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_a_8002_);
                                    lean_dec(v___x_7883_);
                                    v___x_8004_ = lean_box(0);
                                    v_isShared_8005_ = v_isSharedCheck_8009_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_7876_);
                            lean_dec_ref(v___x_7866_);
                            lean_dec(v___x_7861_);
                            lean_dec(v_levelParams_7833_);
                            lean_dec(v___x_7832_);
                            lean_dec_ref(v_xImpl_7831_);
                            lean_dec_ref(v_indices_7830_);
                            lean_dec_ref(v___x_7829_);
                            lean_dec_ref(v_val_7828_);
                            lean_dec(v_ctors_7827_);
                            lean_dec_ref(v_params_7826_);
                            lean_dec_ref(v_compFieldVars_7825_);
                            lean_dec(v_lparams_7824_);
                            v_a_8010_ = lean_ctor_get(v___x_7877_, 0);
                            v_isSharedCheck_8017_ = (!lean_is_exclusive(v___x_7877_)) as u8;
                            if v_isSharedCheck_8017_ == 0 {
                                v___x_8012_ = v___x_7877_;
                                v_isShared_8013_ = v_isSharedCheck_8017_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_8010_);
                                lean_dec(v___x_7877_);
                                v___x_8012_ = lean_box(0);
                                v_isShared_8013_ = v_isSharedCheck_8017_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_7866_);
                        lean_dec(v___x_7861_);
                        lean_dec(v_levelParams_7833_);
                        lean_dec(v___x_7832_);
                        lean_dec_ref(v_xImpl_7831_);
                        lean_dec_ref(v_indices_7830_);
                        lean_dec_ref(v___x_7829_);
                        lean_dec_ref(v_val_7828_);
                        lean_dec(v_ctors_7827_);
                        lean_dec_ref(v_params_7826_);
                        lean_dec_ref(v_compFieldVars_7825_);
                        lean_dec(v_lparams_7824_);
                        v_a_8018_ = lean_ctor_get(v___x_7875_, 0);
                        v_isSharedCheck_8025_ = (!lean_is_exclusive(v___x_7875_)) as u8;
                        if v_isSharedCheck_8025_ == 0 {
                            v___x_8020_ = v___x_7875_;
                            v_isShared_8021_ = v_isSharedCheck_8025_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_8018_);
                            lean_dec(v___x_7875_);
                            v___x_8020_ = lean_box(0);
                            v_isShared_8021_ = v_isSharedCheck_8025_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7861_);
                    v___x_8026_ = lean_mk_empty_array_with_capacity(v___x_7863_);
                    lean_inc(v_a_7862_);
                    v___x_8027_ = lean_array_push(v___x_8026_, v_a_7862_);
                    v___x_8028_ =
                        l_Lean_compileDecls(v___x_8027_, v___x_7854_, v___y_7841_, v___y_7842_);
                    if lean_obj_tag(v___x_8028_) == 0 {
                        lean_dec_ref_known(v___x_8028_, 1);
                        v_a_7845_ = v___x_7866_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___x_7866_);
                        lean_dec(v_levelParams_7833_);
                        lean_dec(v___x_7832_);
                        lean_dec_ref(v_xImpl_7831_);
                        lean_dec_ref(v_indices_7830_);
                        lean_dec_ref(v___x_7829_);
                        lean_dec_ref(v_val_7828_);
                        lean_dec(v_ctors_7827_);
                        lean_dec_ref(v_params_7826_);
                        lean_dec_ref(v_compFieldVars_7825_);
                        lean_dec(v_lparams_7824_);
                        v_a_8029_ = lean_ctor_get(v___x_8028_, 0);
                        v_isSharedCheck_8036_ = (!lean_is_exclusive(v___x_8028_)) as u8;
                        if v_isSharedCheck_8036_ == 0 {
                            v___x_8031_ = v___x_8028_;
                            v_isShared_8032_ = v_isSharedCheck_8036_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_8029_);
                            lean_dec(v___x_8028_);
                            v___x_8031_ = lean_box(0);
                            v_isShared_8032_ = v_isSharedCheck_8036_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            4 => {
                lean_inc(v_a_7862_);
                v___x_7915_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_7862_, v___x_7908_, v___y_7910_, v___y_7911_, v___y_7912_, v___y_7913_, v___y_7914_);
                if lean_obj_tag(v___x_7915_) == 0 {
                    lean_dec_ref_known(v___x_7915_, 1);
                    v_a_7845_ = v___x_7866_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_7866_);
                    lean_dec(v_levelParams_7833_);
                    lean_dec(v___x_7832_);
                    lean_dec_ref(v_xImpl_7831_);
                    lean_dec_ref(v_indices_7830_);
                    lean_dec_ref(v___x_7829_);
                    lean_dec_ref(v_val_7828_);
                    lean_dec(v_ctors_7827_);
                    lean_dec_ref(v_params_7826_);
                    lean_dec_ref(v_compFieldVars_7825_);
                    lean_dec(v_lparams_7824_);
                    v_a_7916_ = lean_ctor_get(v___x_7915_, 0);
                    v_isSharedCheck_7923_ = (!lean_is_exclusive(v___x_7915_)) as u8;
                    if v_isSharedCheck_7923_ == 0 {
                        v___x_7918_ = v___x_7915_;
                        v_isShared_7919_ = v_isSharedCheck_7923_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7916_);
                        lean_dec(v___x_7915_);
                        v___x_7918_ = lean_box(0);
                        v_isShared_7919_ = v_isSharedCheck_7923_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_7919_ == 0 {
                    v___x_7921_ = v___x_7918_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7922_, 0, v_a_7916_);
                    v___x_7921_ = v_reuseFailAlloc_7922_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7921_;
            }
            7 => {
                if v_isShared_7941_ == 0 {
                    v___x_7943_ = v___x_7940_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7944_, 0, v_a_7938_);
                    v___x_7943_ = v_reuseFailAlloc_7944_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7943_;
            }
            9 => {
                if v_isShared_7949_ == 0 {
                    v___x_7951_ = v___x_7948_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7952_, 0, v_a_7946_);
                    v___x_7951_ = v_reuseFailAlloc_7952_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7951_;
            }
            11 => {
                if v_isShared_7957_ == 0 {
                    v___x_7959_ = v___x_7956_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7960_, 0, v_a_7954_);
                    v___x_7959_ = v_reuseFailAlloc_7960_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7959_;
            }
            13 => {
                if v_isShared_7965_ == 0 {
                    v___x_7967_ = v___x_7964_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7968_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7968_, 0, v_a_7962_);
                    v___x_7967_ = v_reuseFailAlloc_7968_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7967_;
            }
            15 => {
                if v_isShared_7973_ == 0 {
                    v___x_7975_ = v___x_7972_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7976_, 0, v_a_7970_);
                    v___x_7975_ = v_reuseFailAlloc_7976_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7975_;
            }
            17 => {
                if v_isShared_7981_ == 0 {
                    v___x_7983_ = v___x_7980_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7984_, 0, v_a_7978_);
                    v___x_7983_ = v_reuseFailAlloc_7984_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7983_;
            }
            19 => {
                if v_isShared_7989_ == 0 {
                    v___x_7991_ = v___x_7988_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7992_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7992_, 0, v_a_7986_);
                    v___x_7991_ = v_reuseFailAlloc_7992_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7991_;
            }
            21 => {
                if v_isShared_7997_ == 0 {
                    v___x_7999_ = v___x_7996_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_8000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8000_, 0, v_a_7994_);
                    v___x_7999_ = v_reuseFailAlloc_8000_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7999_;
            }
            23 => {
                if v_isShared_8005_ == 0 {
                    v___x_8007_ = v___x_8004_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_8008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8008_, 0, v_a_8002_);
                    v___x_8007_ = v_reuseFailAlloc_8008_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_8007_;
            }
            25 => {
                if v_isShared_8013_ == 0 {
                    v___x_8015_ = v___x_8012_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_8016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 0, v_a_8010_);
                    v___x_8015_ = v_reuseFailAlloc_8016_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_8015_;
            }
            27 => {
                if v_isShared_8021_ == 0 {
                    v___x_8023_ = v___x_8020_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_8024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8024_, 0, v_a_8018_);
                    v___x_8023_ = v_reuseFailAlloc_8024_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_8023_;
            }
            29 => {
                if v_isShared_8032_ == 0 {
                    v___x_8034_ = v___x_8031_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_8035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8035_, 0, v_a_8029_);
                    v___x_8034_ = v_reuseFailAlloc_8035_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_8034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lparams_8042_: *mut LeanObject = *_args.add(0);
    let mut v_compFieldVars_8043_: *mut LeanObject = *_args.add(1);
    let mut v_params_8044_: *mut LeanObject = *_args.add(2);
    let mut v_ctors_8045_: *mut LeanObject = *_args.add(3);
    let mut v_val_8046_: *mut LeanObject = *_args.add(4);
    let mut v___x_8047_: *mut LeanObject = *_args.add(5);
    let mut v_indices_8048_: *mut LeanObject = *_args.add(6);
    let mut v_xImpl_8049_: *mut LeanObject = *_args.add(7);
    let mut v___x_8050_: *mut LeanObject = *_args.add(8);
    let mut v_levelParams_8051_: *mut LeanObject = *_args.add(9);
    let mut v_as_8052_: *mut LeanObject = *_args.add(10);
    let mut v_sz_8053_: *mut LeanObject = *_args.add(11);
    let mut v_i_8054_: *mut LeanObject = *_args.add(12);
    let mut v_b_8055_: *mut LeanObject = *_args.add(13);
    let mut v___y_8056_: *mut LeanObject = *_args.add(14);
    let mut v___y_8057_: *mut LeanObject = *_args.add(15);
    let mut v___y_8058_: *mut LeanObject = *_args.add(16);
    let mut v___y_8059_: *mut LeanObject = *_args.add(17);
    let mut v___y_8060_: *mut LeanObject = *_args.add(18);
    let mut v___y_8061_: *mut LeanObject = *_args.add(19);
    let mut v_sz_boxed_8062_: usize = 0;
    let mut v_i_boxed_8063_: usize = 0;
    let mut v_res_8064_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8062_ = lean_unbox_usize(v_sz_8053_);
    lean_dec(v_sz_8053_);
    v_i_boxed_8063_ = lean_unbox_usize(v_i_8054_);
    lean_dec(v_i_8054_);
    v_res_8064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_8042_, v_compFieldVars_8043_, v_params_8044_, v_ctors_8045_, v_val_8046_, v___x_8047_, v_indices_8048_, v_xImpl_8049_, v___x_8050_, v_levelParams_8051_, v_as_8052_, v_sz_boxed_8062_, v_i_boxed_8063_, v_b_8055_, v___y_8056_, v___y_8057_, v___y_8058_, v___y_8059_, v___y_8060_);
    lean_dec(v___y_8060_);
    lean_dec_ref(v___y_8059_);
    lean_dec(v___y_8058_);
    lean_dec_ref(v___y_8057_);
    lean_dec_ref(v___y_8056_);
    lean_dec_ref(v_as_8052_);
    return v_res_8064_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(
    mut v_compFieldVars_8065_: *mut LeanObject,
    mut v_compFields_8066_: *mut LeanObject,
    mut v_lparams_8067_: *mut LeanObject,
    mut v_params_8068_: *mut LeanObject,
    mut v_ctors_8069_: *mut LeanObject,
    mut v_val_8070_: *mut LeanObject,
    mut v___x_8071_: *mut LeanObject,
    mut v_indices_8072_: *mut LeanObject,
    mut v___x_8073_: *mut LeanObject,
    mut v_levelParams_8074_: *mut LeanObject,
    mut v_xImpl_8075_: *mut LeanObject,
    mut v___y_8076_: *mut LeanObject,
    mut v___y_8077_: *mut LeanObject,
    mut v___y_8078_: *mut LeanObject,
    mut v___y_8079_: *mut LeanObject,
    mut v___y_8080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8085_: usize = 0;
    let mut v___x_8086_: usize = 0;
    let mut v___x_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8090_: u8 = 0;
    let mut v___x_8091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8095_: u8 = 0;
    let mut v_unused_8096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8100_: u8 = 0;
    let mut v___x_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8082_ = lean_unsigned_to_nat(0);
                v___x_8083_ = lean_array_get_size(v_compFieldVars_8065_);
                lean_inc_ref(v_compFieldVars_8065_);
                v___x_8084_ =
                    l_Array_toSubarray___redArg(v_compFieldVars_8065_, v___x_8082_, v___x_8083_);
                v_sz_8085_ = lean_array_size(v_compFields_8066_);
                v___x_8086_ = 0usize;
                v___x_8087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_8067_, v_compFieldVars_8065_, v_params_8068_, v_ctors_8069_, v_val_8070_, v___x_8071_, v_indices_8072_, v_xImpl_8075_, v___x_8073_, v_levelParams_8074_, v_compFields_8066_, v_sz_8085_, v___x_8086_, v___x_8084_, v___y_8076_, v___y_8077_, v___y_8078_, v___y_8079_, v___y_8080_);
                if lean_obj_tag(v___x_8087_) == 0 {
                    v_isSharedCheck_8095_ = (!lean_is_exclusive(v___x_8087_)) as u8;
                    if v_isSharedCheck_8095_ == 0 {
                        v_unused_8096_ = lean_ctor_get(v___x_8087_, 0);
                        lean_dec(v_unused_8096_);
                        v___x_8089_ = v___x_8087_;
                        v_isShared_8090_ = v_isSharedCheck_8095_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_8087_);
                        v___x_8089_ = lean_box(0);
                        v_isShared_8090_ = v_isSharedCheck_8095_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8097_ = lean_ctor_get(v___x_8087_, 0);
                    v_isSharedCheck_8104_ = (!lean_is_exclusive(v___x_8087_)) as u8;
                    if v_isSharedCheck_8104_ == 0 {
                        v___x_8099_ = v___x_8087_;
                        v_isShared_8100_ = v_isSharedCheck_8104_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8097_);
                        lean_dec(v___x_8087_);
                        v___x_8099_ = lean_box(0);
                        v_isShared_8100_ = v_isSharedCheck_8104_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8091_ = lean_box(0);
                if v_isShared_8090_ == 0 {
                    lean_ctor_set(v___x_8089_, 0, v___x_8091_);
                    v___x_8093_ = v___x_8089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8094_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8094_, 0, v___x_8091_);
                    v___x_8093_ = v_reuseFailAlloc_8094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8093_;
            }
            3 => {
                if v_isShared_8100_ == 0 {
                    v___x_8102_ = v___x_8099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8103_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8103_, 0, v_a_8097_);
                    v___x_8102_ = v_reuseFailAlloc_8103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_compFieldVars_8105_: *mut LeanObject = *_args.add(0);
    let mut v_compFields_8106_: *mut LeanObject = *_args.add(1);
    let mut v_lparams_8107_: *mut LeanObject = *_args.add(2);
    let mut v_params_8108_: *mut LeanObject = *_args.add(3);
    let mut v_ctors_8109_: *mut LeanObject = *_args.add(4);
    let mut v_val_8110_: *mut LeanObject = *_args.add(5);
    let mut v___x_8111_: *mut LeanObject = *_args.add(6);
    let mut v_indices_8112_: *mut LeanObject = *_args.add(7);
    let mut v___x_8113_: *mut LeanObject = *_args.add(8);
    let mut v_levelParams_8114_: *mut LeanObject = *_args.add(9);
    let mut v_xImpl_8115_: *mut LeanObject = *_args.add(10);
    let mut v___y_8116_: *mut LeanObject = *_args.add(11);
    let mut v___y_8117_: *mut LeanObject = *_args.add(12);
    let mut v___y_8118_: *mut LeanObject = *_args.add(13);
    let mut v___y_8119_: *mut LeanObject = *_args.add(14);
    let mut v___y_8120_: *mut LeanObject = *_args.add(15);
    let mut v___y_8121_: *mut LeanObject = *_args.add(16);
    let mut v_res_8122_: *mut LeanObject = core::ptr::null_mut();
    v_res_8122_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(
        v_compFieldVars_8105_,
        v_compFields_8106_,
        v_lparams_8107_,
        v_params_8108_,
        v_ctors_8109_,
        v_val_8110_,
        v___x_8111_,
        v_indices_8112_,
        v___x_8113_,
        v_levelParams_8114_,
        v_xImpl_8115_,
        v___y_8116_,
        v___y_8117_,
        v___y_8118_,
        v___y_8119_,
        v___y_8120_,
    );
    lean_dec(v___y_8120_);
    lean_dec_ref(v___y_8119_);
    lean_dec(v___y_8118_);
    lean_dec_ref(v___y_8117_);
    lean_dec_ref(v___y_8116_);
    lean_dec_ref(v_compFields_8106_);
    return v_res_8122_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideComputedFields(
    mut v_a_8126_: *mut LeanObject,
    mut v_a_8127_: *mut LeanObject,
    mut v_a_8128_: *mut LeanObject,
    mut v_a_8129_: *mut LeanObject,
    mut v_a_8130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInductiveVal_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lparams_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_compFields_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_compFieldVars_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8150_: *mut LeanObject = core::ptr::null_mut();
    v_toInductiveVal_8132_ = lean_ctor_get(v_a_8126_, 0);
    v_toConstantVal_8133_ = lean_ctor_get(v_toInductiveVal_8132_, 0);
    v_lparams_8134_ = lean_ctor_get(v_a_8126_, 1);
    v_params_8135_ = lean_ctor_get(v_a_8126_, 2);
    v_compFields_8136_ = lean_ctor_get(v_a_8126_, 3);
    v_compFieldVars_8137_ = lean_ctor_get(v_a_8126_, 4);
    v_indices_8138_ = lean_ctor_get(v_a_8126_, 5);
    v_val_8139_ = lean_ctor_get(v_a_8126_, 6);
    v_ctors_8140_ = lean_ctor_get(v_toInductiveVal_8132_, 4);
    v_name_8141_ = lean_ctor_get(v_toConstantVal_8133_, 0);
    v_levelParams_8142_ = lean_ctor_get(v_toConstantVal_8133_, 1);
    v___x_8143_ = l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1;
    v___x_8144_ =
        l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1;
    lean_inc(v_name_8141_);
    v___x_8145_ = l_Lean_Name_append(v_name_8141_, v___x_8144_);
    lean_inc_n(v_lparams_8134_, 2);
    lean_inc(v___x_8145_);
    v___x_8146_ = l_Lean_mkConst(v___x_8145_, v_lparams_8134_);
    lean_inc_ref_n(v_params_8135_, 2);
    v___x_8147_ = l_Array_append___redArg(v_params_8135_, v_indices_8138_);
    lean_inc(v_levelParams_8142_);
    lean_inc_ref(v_indices_8138_);
    lean_inc_ref(v___x_8147_);
    lean_inc_ref(v_val_8139_);
    lean_inc(v_ctors_8140_);
    lean_inc_ref(v_compFields_8136_);
    lean_inc_ref(v_compFieldVars_8137_);
    v___f_8148_ = lean_alloc_closure(
        l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed
            as *mut core::ffi::c_void,
        17,
        10,
    );
    lean_closure_set(v___f_8148_, 0, v_compFieldVars_8137_);
    lean_closure_set(v___f_8148_, 1, v_compFields_8136_);
    lean_closure_set(v___f_8148_, 2, v_lparams_8134_);
    lean_closure_set(v___f_8148_, 3, v_params_8135_);
    lean_closure_set(v___f_8148_, 4, v_ctors_8140_);
    lean_closure_set(v___f_8148_, 5, v_val_8139_);
    lean_closure_set(v___f_8148_, 6, v___x_8147_);
    lean_closure_set(v___f_8148_, 7, v_indices_8138_);
    lean_closure_set(v___f_8148_, 8, v___x_8145_);
    lean_closure_set(v___f_8148_, 9, v_levelParams_8142_);
    v___x_8149_ = l_Lean_mkAppN(v___x_8146_, v___x_8147_);
    lean_dec_ref(v___x_8147_);
    v___x_8150_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_8143_, v___x_8149_, v___f_8148_, v_a_8126_, v_a_8127_, v_a_8128_, v_a_8129_, v_a_8130_);
    return v___x_8150_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(
    mut v_a_8151_: *mut LeanObject,
    mut v_a_8152_: *mut LeanObject,
    mut v_a_8153_: *mut LeanObject,
    mut v_a_8154_: *mut LeanObject,
    mut v_a_8155_: *mut LeanObject,
    mut v_a_8156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8157_: *mut LeanObject = core::ptr::null_mut();
    v_res_8157_ = l_Lean_Elab_ComputedFields_overrideComputedFields(
        v_a_8151_, v_a_8152_, v_a_8153_, v_a_8154_, v_a_8155_,
    );
    lean_dec(v_a_8155_);
    lean_dec_ref(v_a_8154_);
    lean_dec(v_a_8153_);
    lean_dec_ref(v_a_8152_);
    lean_dec_ref(v_a_8151_);
    return v_res_8157_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(
    mut v_k_8158_: *mut LeanObject,
    mut v_b_8159_: *mut LeanObject,
    mut v_c_8160_: *mut LeanObject,
    mut v___y_8161_: *mut LeanObject,
    mut v___y_8162_: *mut LeanObject,
    mut v___y_8163_: *mut LeanObject,
    mut v___y_8164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8166_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_8164_);
    lean_inc_ref(v___y_8163_);
    lean_inc(v___y_8162_);
    lean_inc_ref(v___y_8161_);
    v___x_8166_ = lean_apply_7(
        v_k_8158_,
        v_b_8159_,
        v_c_8160_,
        v___y_8161_,
        v___y_8162_,
        v___y_8163_,
        v___y_8164_,
        lean_box(0),
    );
    return v___x_8166_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(
    mut v_k_8167_: *mut LeanObject,
    mut v_b_8168_: *mut LeanObject,
    mut v_c_8169_: *mut LeanObject,
    mut v___y_8170_: *mut LeanObject,
    mut v___y_8171_: *mut LeanObject,
    mut v___y_8172_: *mut LeanObject,
    mut v___y_8173_: *mut LeanObject,
    mut v___y_8174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8175_: *mut LeanObject = core::ptr::null_mut();
    v_res_8175_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_8167_, v_b_8168_, v_c_8169_, v___y_8170_, v___y_8171_, v___y_8172_, v___y_8173_);
    lean_dec(v___y_8173_);
    lean_dec_ref(v___y_8172_);
    lean_dec(v___y_8171_);
    lean_dec_ref(v___y_8170_);
    return v_res_8175_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(
    mut v_type_8176_: *mut LeanObject,
    mut v_k_8177_: *mut LeanObject,
    mut v_cleanupAnnotations_8178_: u8,
    mut v___y_8179_: *mut LeanObject,
    mut v___y_8180_: *mut LeanObject,
    mut v___y_8181_: *mut LeanObject,
    mut v___y_8182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: u8 = 0;
    let mut v___x_8186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8191_: u8 = 0;
    let mut v___x_8193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8195_: u8 = 0;
    let mut v_a_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8199_: u8 = 0;
    let mut v___x_8201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8184_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_8184_, 0, v_k_8177_);
                v___x_8185_ = 0;
                v___x_8186_ = lean_box(0);
                v___x_8187_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_8185_,
                        v___x_8186_,
                        v_type_8176_,
                        v___f_8184_,
                        v_cleanupAnnotations_8178_,
                        v___x_8185_,
                        v___y_8179_,
                        v___y_8180_,
                        v___y_8181_,
                        v___y_8182_,
                    );
                if lean_obj_tag(v___x_8187_) == 0 {
                    v_a_8188_ = lean_ctor_get(v___x_8187_, 0);
                    v_isSharedCheck_8195_ = (!lean_is_exclusive(v___x_8187_)) as u8;
                    if v_isSharedCheck_8195_ == 0 {
                        v___x_8190_ = v___x_8187_;
                        v_isShared_8191_ = v_isSharedCheck_8195_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8188_);
                        lean_dec(v___x_8187_);
                        v___x_8190_ = lean_box(0);
                        v_isShared_8191_ = v_isSharedCheck_8195_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8196_ = lean_ctor_get(v___x_8187_, 0);
                    v_isSharedCheck_8203_ = (!lean_is_exclusive(v___x_8187_)) as u8;
                    if v_isSharedCheck_8203_ == 0 {
                        v___x_8198_ = v___x_8187_;
                        v_isShared_8199_ = v_isSharedCheck_8203_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8196_);
                        lean_dec(v___x_8187_);
                        v___x_8198_ = lean_box(0);
                        v_isShared_8199_ = v_isSharedCheck_8203_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8191_ == 0 {
                    v___x_8193_ = v___x_8190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8194_, 0, v_a_8188_);
                    v___x_8193_ = v_reuseFailAlloc_8194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8193_;
            }
            3 => {
                if v_isShared_8199_ == 0 {
                    v___x_8201_ = v___x_8198_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8202_, 0, v_a_8196_);
                    v___x_8201_ = v_reuseFailAlloc_8202_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(
    mut v_type_8204_: *mut LeanObject,
    mut v_k_8205_: *mut LeanObject,
    mut v_cleanupAnnotations_8206_: *mut LeanObject,
    mut v___y_8207_: *mut LeanObject,
    mut v___y_8208_: *mut LeanObject,
    mut v___y_8209_: *mut LeanObject,
    mut v___y_8210_: *mut LeanObject,
    mut v___y_8211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_8212_: u8 = 0;
    let mut v_res_8213_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_8212_ = (lean_unbox(v_cleanupAnnotations_8206_) as u8);
    v_res_8213_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_8204_, v_k_8205_, v_cleanupAnnotations_boxed_8212_, v___y_8207_, v___y_8208_, v___y_8209_, v___y_8210_);
    lean_dec(v___y_8210_);
    lean_dec_ref(v___y_8209_);
    lean_dec(v___y_8208_);
    lean_dec_ref(v___y_8207_);
    return v_res_8213_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(
    mut v_00_u03b1_8214_: *mut LeanObject,
    mut v_type_8215_: *mut LeanObject,
    mut v_k_8216_: *mut LeanObject,
    mut v_cleanupAnnotations_8217_: u8,
    mut v___y_8218_: *mut LeanObject,
    mut v___y_8219_: *mut LeanObject,
    mut v___y_8220_: *mut LeanObject,
    mut v___y_8221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8223_: *mut LeanObject = core::ptr::null_mut();
    v___x_8223_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_8215_, v_k_8216_, v_cleanupAnnotations_8217_, v___y_8218_, v___y_8219_, v___y_8220_, v___y_8221_);
    return v___x_8223_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(
    mut v_00_u03b1_8224_: *mut LeanObject,
    mut v_type_8225_: *mut LeanObject,
    mut v_k_8226_: *mut LeanObject,
    mut v_cleanupAnnotations_8227_: *mut LeanObject,
    mut v___y_8228_: *mut LeanObject,
    mut v___y_8229_: *mut LeanObject,
    mut v___y_8230_: *mut LeanObject,
    mut v___y_8231_: *mut LeanObject,
    mut v___y_8232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_8233_: u8 = 0;
    let mut v_res_8234_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_8233_ = (lean_unbox(v_cleanupAnnotations_8227_) as u8);
    v_res_8234_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_8224_, v_type_8225_, v_k_8226_, v_cleanupAnnotations_boxed_8233_, v___y_8228_, v___y_8229_, v___y_8230_, v___y_8231_);
    lean_dec(v___y_8231_);
    lean_dec_ref(v___y_8230_);
    lean_dec(v___y_8229_);
    lean_dec_ref(v___y_8228_);
    return v_res_8234_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(
    mut v_a_8235_: *mut LeanObject,
    mut v___x_8236_: *mut LeanObject,
    mut v___x_8237_: *mut LeanObject,
    mut v_compFields_8238_: *mut LeanObject,
    mut v___x_8239_: *mut LeanObject,
    mut v_val_8240_: *mut LeanObject,
    mut v_compFieldVars_8241_: *mut LeanObject,
    mut v___y_8242_: *mut LeanObject,
    mut v___y_8243_: *mut LeanObject,
    mut v___y_8244_: *mut LeanObject,
    mut v___y_8245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: *mut LeanObject = core::ptr::null_mut();
    v___x_8247_ = lean_alloc_ctor(0, 7, (0) as u32);
    lean_ctor_set(v___x_8247_, 0, v_a_8235_);
    lean_ctor_set(v___x_8247_, 1, v___x_8236_);
    lean_ctor_set(v___x_8247_, 2, v___x_8237_);
    lean_ctor_set(v___x_8247_, 3, v_compFields_8238_);
    lean_ctor_set(v___x_8247_, 4, v_compFieldVars_8241_);
    lean_ctor_set(v___x_8247_, 5, v___x_8239_);
    lean_ctor_set(v___x_8247_, 6, v_val_8240_);
    v___x_8248_ = l_Lean_Elab_ComputedFields_validateComputedFields(
        v___x_8247_,
        v___y_8242_,
        v___y_8243_,
        v___y_8244_,
        v___y_8245_,
    );
    if lean_obj_tag(v___x_8248_) == 0 {
        let mut v___x_8249_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_8248_, 1);
        v___x_8249_ = l_Lean_Elab_ComputedFields_mkImplType(
            v___x_8247_,
            v___y_8242_,
            v___y_8243_,
            v___y_8244_,
            v___y_8245_,
        );
        if lean_obj_tag(v___x_8249_) == 0 {
            let mut v___x_8250_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_8249_, 1);
            v___x_8250_ = l_Lean_Elab_ComputedFields_overrideCasesOn(
                v___x_8247_,
                v___y_8242_,
                v___y_8243_,
                v___y_8244_,
                v___y_8245_,
            );
            if lean_obj_tag(v___x_8250_) == 0 {
                let mut v___x_8251_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_8250_, 1);
                v___x_8251_ = l_Lean_Elab_ComputedFields_overrideConstructors(
                    v___x_8247_,
                    v___y_8242_,
                    v___y_8243_,
                    v___y_8244_,
                    v___y_8245_,
                );
                if lean_obj_tag(v___x_8251_) == 0 {
                    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_8251_, 1);
                    v___x_8252_ = l_Lean_Elab_ComputedFields_overrideComputedFields(
                        v___x_8247_,
                        v___y_8242_,
                        v___y_8243_,
                        v___y_8244_,
                        v___y_8245_,
                    );
                    lean_dec_ref_known(v___x_8247_, 7);
                    return v___x_8252_;
                } else {
                    lean_dec_ref_known(v___x_8247_, 7);
                    return v___x_8251_;
                }
            } else {
                lean_dec_ref_known(v___x_8247_, 7);
                return v___x_8250_;
            }
        } else {
            lean_dec_ref_known(v___x_8247_, 7);
            return v___x_8249_;
        }
    } else {
        lean_dec_ref_known(v___x_8247_, 7);
        return v___x_8248_;
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(
    mut v_a_8253_: *mut LeanObject,
    mut v___x_8254_: *mut LeanObject,
    mut v___x_8255_: *mut LeanObject,
    mut v_compFields_8256_: *mut LeanObject,
    mut v___x_8257_: *mut LeanObject,
    mut v_val_8258_: *mut LeanObject,
    mut v_compFieldVars_8259_: *mut LeanObject,
    mut v___y_8260_: *mut LeanObject,
    mut v___y_8261_: *mut LeanObject,
    mut v___y_8262_: *mut LeanObject,
    mut v___y_8263_: *mut LeanObject,
    mut v___y_8264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8265_: *mut LeanObject = core::ptr::null_mut();
    v_res_8265_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(
        v_a_8253_,
        v___x_8254_,
        v___x_8255_,
        v_compFields_8256_,
        v___x_8257_,
        v_val_8258_,
        v_compFieldVars_8259_,
        v___y_8260_,
        v___y_8261_,
        v___y_8262_,
        v___y_8263_,
    );
    lean_dec(v___y_8263_);
    lean_dec_ref(v___y_8262_);
    lean_dec(v___y_8261_);
    lean_dec_ref(v___y_8260_);
    return v_res_8265_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(
    mut v___x_8266_: *mut LeanObject,
    mut v___x_8267_: *mut LeanObject,
    mut v_val_8268_: *mut LeanObject,
    mut v_v_8269_: *mut LeanObject,
    mut v_x_8270_: *mut LeanObject,
    mut v___y_8271_: *mut LeanObject,
    mut v___y_8272_: *mut LeanObject,
    mut v___y_8273_: *mut LeanObject,
    mut v___y_8274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut LeanObject = core::ptr::null_mut();
    v___x_8276_ = l_Array_append___redArg(v___x_8266_, v___x_8267_);
    v___x_8277_ = lean_unsigned_to_nat(1);
    v___x_8278_ = lean_mk_empty_array_with_capacity(v___x_8277_);
    v___x_8279_ = lean_array_push(v___x_8278_, v_val_8268_);
    v___x_8280_ = l_Array_append___redArg(v___x_8276_, v___x_8279_);
    lean_dec_ref(v___x_8279_);
    v___x_8281_ = l_Lean_Meta_mkAppM(
        v_v_8269_,
        v___x_8280_,
        v___y_8271_,
        v___y_8272_,
        v___y_8273_,
        v___y_8274_,
    );
    if lean_obj_tag(v___x_8281_) == 0 {
        let mut v_a_8282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8283_: *mut LeanObject = core::ptr::null_mut();
        v_a_8282_ = lean_ctor_get(v___x_8281_, 0);
        lean_inc(v_a_8282_);
        lean_dec_ref_known(v___x_8281_, 1);
        lean_inc(v___y_8274_);
        lean_inc_ref(v___y_8273_);
        lean_inc(v___y_8272_);
        lean_inc_ref(v___y_8271_);
        v___x_8283_ = lean_infer_type(
            v_a_8282_,
            v___y_8271_,
            v___y_8272_,
            v___y_8273_,
            v___y_8274_,
        );
        return v___x_8283_;
    } else {
        return v___x_8281_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(
    mut v___x_8284_: *mut LeanObject,
    mut v___x_8285_: *mut LeanObject,
    mut v_val_8286_: *mut LeanObject,
    mut v_v_8287_: *mut LeanObject,
    mut v_x_8288_: *mut LeanObject,
    mut v___y_8289_: *mut LeanObject,
    mut v___y_8290_: *mut LeanObject,
    mut v___y_8291_: *mut LeanObject,
    mut v___y_8292_: *mut LeanObject,
    mut v___y_8293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8294_: *mut LeanObject = core::ptr::null_mut();
    v_res_8294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_8284_, v___x_8285_, v_val_8286_, v_v_8287_, v_x_8288_, v___y_8289_, v___y_8290_, v___y_8291_, v___y_8292_);
    lean_dec(v___y_8292_);
    lean_dec_ref(v___y_8291_);
    lean_dec(v___y_8290_);
    lean_dec_ref(v___y_8289_);
    lean_dec_ref(v_x_8288_);
    lean_dec_ref(v___x_8285_);
    return v_res_8294_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(
    mut v___x_8295_: *mut LeanObject,
    mut v___x_8296_: *mut LeanObject,
    mut v_val_8297_: *mut LeanObject,
    mut v_sz_8298_: usize,
    mut v_i_8299_: usize,
    mut v_bs_8300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8301_: u8 = 0;
    let mut v_v_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: usize = 0;
    let mut v___x_8310_: usize = 0;
    let mut v___x_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8301_ = lean_usize_dec_lt(v_i_8299_, v_sz_8298_);
                if v___x_8301_ == 0 {
                    lean_dec_ref(v_val_8297_);
                    lean_dec_ref(v___x_8296_);
                    lean_dec_ref(v___x_8295_);
                    return v_bs_8300_;
                } else {
                    v_v_8302_ = lean_array_uget(v_bs_8300_, v_i_8299_);
                    lean_inc(v_v_8302_);
                    lean_inc_ref(v_val_8297_);
                    lean_inc_ref(v___x_8296_);
                    lean_inc_ref(v___x_8295_);
                    v___f_8303_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                    lean_closure_set(v___f_8303_, 0, v___x_8295_);
                    lean_closure_set(v___f_8303_, 1, v___x_8296_);
                    lean_closure_set(v___f_8303_, 2, v_val_8297_);
                    lean_closure_set(v___f_8303_, 3, v_v_8302_);
                    v___x_8304_ = lean_unsigned_to_nat(0);
                    v_bs_x27_8305_ = lean_array_uset(v_bs_8300_, v_i_8299_, v___x_8304_);
                    v___x_8306_ = lean_box(0);
                    v___x_8307_ = l_Lean_Name_updatePrefix(v_v_8302_, v___x_8306_);
                    v___x_8308_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8308_, 0, v___x_8307_);
                    lean_ctor_set(v___x_8308_, 1, v___f_8303_);
                    v___x_8309_ = 1usize;
                    v___x_8310_ = lean_usize_add(v_i_8299_, v___x_8309_);
                    v___x_8311_ = lean_array_uset(v_bs_x27_8305_, v_i_8299_, v___x_8308_);
                    v_i_8299_ = v___x_8310_;
                    v_bs_8300_ = v___x_8311_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(
    mut v___x_8313_: *mut LeanObject,
    mut v___x_8314_: *mut LeanObject,
    mut v_val_8315_: *mut LeanObject,
    mut v_sz_8316_: *mut LeanObject,
    mut v_i_8317_: *mut LeanObject,
    mut v_bs_8318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8319_: usize = 0;
    let mut v_i_boxed_8320_: usize = 0;
    let mut v_res_8321_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8319_ = lean_unbox_usize(v_sz_8316_);
    lean_dec(v_sz_8316_);
    v_i_boxed_8320_ = lean_unbox_usize(v_i_8317_);
    lean_dec(v_i_8317_);
    v_res_8321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_8313_, v___x_8314_, v_val_8315_, v_sz_boxed_8319_, v_i_boxed_8320_, v_bs_8318_);
    return v_res_8321_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(
    mut v_sz_8322_: usize,
    mut v_i_8323_: usize,
    mut v_bs_8324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8325_: u8 = 0;
    let mut v_v_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8331_: u8 = 0;
    let mut v___x_8332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8334_: u8 = 0;
    let mut v___x_8335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8339_: usize = 0;
    let mut v___x_8340_: usize = 0;
    let mut v___x_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8325_ = lean_usize_dec_lt(v_i_8323_, v_sz_8322_);
                if v___x_8325_ == 0 {
                    return v_bs_8324_;
                } else {
                    v_v_8326_ = lean_array_uget(v_bs_8324_, v_i_8323_);
                    v_fst_8327_ = lean_ctor_get(v_v_8326_, 0);
                    v_snd_8328_ = lean_ctor_get(v_v_8326_, 1);
                    v_isSharedCheck_8344_ = (!lean_is_exclusive(v_v_8326_)) as u8;
                    if v_isSharedCheck_8344_ == 0 {
                        v___x_8330_ = v_v_8326_;
                        v_isShared_8331_ = v_isSharedCheck_8344_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_8328_);
                        lean_inc(v_fst_8327_);
                        lean_dec(v_v_8326_);
                        v___x_8330_ = lean_box(0);
                        v_isShared_8331_ = v_isSharedCheck_8344_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8332_ = lean_unsigned_to_nat(0);
                v_bs_x27_8333_ = lean_array_uset(v_bs_8324_, v_i_8323_, v___x_8332_);
                v___x_8334_ = 0;
                v___x_8335_ = lean_box((v___x_8334_) as usize);
                if v_isShared_8331_ == 0 {
                    lean_ctor_set(v___x_8330_, 0, v___x_8335_);
                    v___x_8337_ = v___x_8330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8343_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8343_, 0, v___x_8335_);
                    lean_ctor_set(v_reuseFailAlloc_8343_, 1, v_snd_8328_);
                    v___x_8337_ = v_reuseFailAlloc_8343_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8338_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8338_, 0, v_fst_8327_);
                lean_ctor_set(v___x_8338_, 1, v___x_8337_);
                v___x_8339_ = 1usize;
                v___x_8340_ = lean_usize_add(v_i_8323_, v___x_8339_);
                v___x_8341_ = lean_array_uset(v_bs_x27_8333_, v_i_8323_, v___x_8338_);
                v_i_8323_ = v___x_8340_;
                v_bs_8324_ = v___x_8341_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(
    mut v_sz_8345_: *mut LeanObject,
    mut v_i_8346_: *mut LeanObject,
    mut v_bs_8347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8348_: usize = 0;
    let mut v_i_boxed_8349_: usize = 0;
    let mut v_res_8350_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8348_ = lean_unbox_usize(v_sz_8345_);
    lean_dec(v_sz_8345_);
    v_i_boxed_8349_ = lean_unbox_usize(v_i_8346_);
    lean_dec(v_i_8346_);
    v_res_8350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_8348_, v_i_boxed_8349_, v_bs_8347_);
    return v_res_8350_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(
    mut v___x_8351_: *mut LeanObject,
    mut v_a_8352_: *mut LeanObject,
    mut v___y_8353_: *mut LeanObject,
    mut v___y_8354_: *mut LeanObject,
    mut v___y_8355_: *mut LeanObject,
    mut v___y_8356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000__overap_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut LeanObject = core::ptr::null_mut();
    v___x_8358_ = l_Lean_instInhabitedExpr;
    v___x_3000__overap_8359_ = l_instInhabitedOfMonad___redArg(v___x_8351_, v___x_8358_);
    lean_inc(v___y_8356_);
    lean_inc_ref(v___y_8355_);
    lean_inc(v___y_8354_);
    lean_inc_ref(v___y_8353_);
    v___x_8360_ = lean_apply_5(
        v___x_3000__overap_8359_,
        v___y_8353_,
        v___y_8354_,
        v___y_8355_,
        v___y_8356_,
        lean_box(0),
    );
    return v___x_8360_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed(
    mut v___x_8361_: *mut LeanObject,
    mut v_a_8362_: *mut LeanObject,
    mut v___y_8363_: *mut LeanObject,
    mut v___y_8364_: *mut LeanObject,
    mut v___y_8365_: *mut LeanObject,
    mut v___y_8366_: *mut LeanObject,
    mut v___y_8367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8368_: *mut LeanObject = core::ptr::null_mut();
    v_res_8368_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0(v___x_8361_, v_a_8362_, v___y_8363_, v___y_8364_, v___y_8365_, v___y_8366_);
    lean_dec(v___y_8366_);
    lean_dec_ref(v___y_8365_);
    lean_dec(v___y_8364_);
    lean_dec_ref(v___y_8363_);
    lean_dec_ref(v_a_8362_);
    return v_res_8368_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed(
    mut v_acc_8369_: *mut LeanObject,
    mut v_declInfos_8370_: *mut LeanObject,
    mut v_k_8371_: *mut LeanObject,
    mut v_kind_8372_: *mut LeanObject,
    mut v_b_8373_: *mut LeanObject,
    mut v___y_8374_: *mut LeanObject,
    mut v___y_8375_: *mut LeanObject,
    mut v___y_8376_: *mut LeanObject,
    mut v___y_8377_: *mut LeanObject,
    mut v___y_8378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8379_: u8 = 0;
    let mut v_res_8380_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8379_ = (lean_unbox(v_kind_8372_) as u8);
    v_res_8380_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(v_acc_8369_, v_declInfos_8370_, v_k_8371_, v_kind_boxed_8379_, v_b_8373_, v___y_8374_, v___y_8375_, v___y_8376_, v___y_8377_);
    lean_dec(v___y_8377_);
    lean_dec_ref(v___y_8376_);
    lean_dec(v___y_8375_);
    lean_dec_ref(v___y_8374_);
    return v_res_8380_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(
    mut v_acc_8381_: *mut LeanObject,
    mut v_declInfos_8382_: *mut LeanObject,
    mut v_k_8383_: *mut LeanObject,
    mut v_kind_8384_: u8,
    mut v_name_8385_: *mut LeanObject,
    mut v_bi_8386_: u8,
    mut v_type_8387_: *mut LeanObject,
    mut v_kind_8388_: u8,
    mut v___y_8389_: *mut LeanObject,
    mut v___y_8390_: *mut LeanObject,
    mut v___y_8391_: *mut LeanObject,
    mut v___y_8392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8400_: u8 = 0;
    let mut v___x_8402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8404_: u8 = 0;
    let mut v_a_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8408_: u8 = 0;
    let mut v___x_8410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8394_ = lean_box((v_kind_8384_) as usize);
                v___f_8395_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                lean_closure_set(v___f_8395_, 0, v_acc_8381_);
                lean_closure_set(v___f_8395_, 1, v_declInfos_8382_);
                lean_closure_set(v___f_8395_, 2, v_k_8383_);
                lean_closure_set(v___f_8395_, 3, v___x_8394_);
                v___x_8396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_8385_,
                    v_bi_8386_,
                    v_type_8387_,
                    v___f_8395_,
                    v_kind_8388_,
                    v___y_8389_,
                    v___y_8390_,
                    v___y_8391_,
                    v___y_8392_,
                );
                if lean_obj_tag(v___x_8396_) == 0 {
                    v_a_8397_ = lean_ctor_get(v___x_8396_, 0);
                    v_isSharedCheck_8404_ = (!lean_is_exclusive(v___x_8396_)) as u8;
                    if v_isSharedCheck_8404_ == 0 {
                        v___x_8399_ = v___x_8396_;
                        v_isShared_8400_ = v_isSharedCheck_8404_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8397_);
                        lean_dec(v___x_8396_);
                        v___x_8399_ = lean_box(0);
                        v_isShared_8400_ = v_isSharedCheck_8404_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8405_ = lean_ctor_get(v___x_8396_, 0);
                    v_isSharedCheck_8412_ = (!lean_is_exclusive(v___x_8396_)) as u8;
                    if v_isSharedCheck_8412_ == 0 {
                        v___x_8407_ = v___x_8396_;
                        v_isShared_8408_ = v_isSharedCheck_8412_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8405_);
                        lean_dec(v___x_8396_);
                        v___x_8407_ = lean_box(0);
                        v_isShared_8408_ = v_isSharedCheck_8412_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8400_ == 0 {
                    v___x_8402_ = v___x_8399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8403_, 0, v_a_8397_);
                    v___x_8402_ = v_reuseFailAlloc_8403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8402_;
            }
            3 => {
                if v_isShared_8408_ == 0 {
                    v___x_8410_ = v___x_8407_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8411_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8411_, 0, v_a_8405_);
                    v___x_8410_ = v_reuseFailAlloc_8411_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(
    mut v_declInfos_8413_: *mut LeanObject,
    mut v_k_8414_: *mut LeanObject,
    mut v_kind_8415_: u8,
    mut v_acc_8416_: *mut LeanObject,
    mut v___y_8417_: *mut LeanObject,
    mut v___y_8418_: *mut LeanObject,
    mut v___y_8419_: *mut LeanObject,
    mut v___y_8420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8427_: u8 = 0;
    let mut v_toFunctor_8428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8434_: u8 = 0;
    let mut v___f_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8451_: u8 = 0;
    let mut v_toFunctor_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8458_: u8 = 0;
    let mut v___f_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8473_: u8 = 0;
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: u8 = 0;
    let mut v___f_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8489_: u8 = 0;
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8494_: u8 = 0;
    let mut v___x_8496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8498_: u8 = 0;
    let mut v_reuseFailAlloc_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8501_: u8 = 0;
    let mut v_unused_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8503_: u8 = 0;
    let mut v_unused_8504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8507_: u8 = 0;
    let mut v_unused_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8509_: u8 = 0;
    let mut v_unused_8510_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8422_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
                v___x_8423_ = l_StateRefT_x27_instMonad___redArg(v___x_8422_);
                v_toApplicative_8424_ = lean_ctor_get(v___x_8423_, 0);
                v_isSharedCheck_8509_ = (!lean_is_exclusive(v___x_8423_)) as u8;
                if v_isSharedCheck_8509_ == 0 {
                    v_unused_8510_ = lean_ctor_get(v___x_8423_, 1);
                    lean_dec(v_unused_8510_);
                    v___x_8426_ = v___x_8423_;
                    v_isShared_8427_ = v_isSharedCheck_8509_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_8424_);
                    lean_dec(v___x_8423_);
                    v___x_8426_ = lean_box(0);
                    v_isShared_8427_ = v_isSharedCheck_8509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_8428_ = lean_ctor_get(v_toApplicative_8424_, 0);
                v_toSeq_8429_ = lean_ctor_get(v_toApplicative_8424_, 2);
                v_toSeqLeft_8430_ = lean_ctor_get(v_toApplicative_8424_, 3);
                v_toSeqRight_8431_ = lean_ctor_get(v_toApplicative_8424_, 4);
                v_isSharedCheck_8507_ = (!lean_is_exclusive(v_toApplicative_8424_)) as u8;
                if v_isSharedCheck_8507_ == 0 {
                    v_unused_8508_ = lean_ctor_get(v_toApplicative_8424_, 1);
                    lean_dec(v_unused_8508_);
                    v___x_8433_ = v_toApplicative_8424_;
                    v_isShared_8434_ = v_isSharedCheck_8507_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_8431_);
                    lean_inc(v_toSeqLeft_8430_);
                    lean_inc(v_toSeq_8429_);
                    lean_inc(v_toFunctor_8428_);
                    lean_dec(v_toApplicative_8424_);
                    v___x_8433_ = lean_box(0);
                    v_isShared_8434_ = v_isSharedCheck_8507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_8435_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1;
                v___f_8436_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2;
                lean_inc_ref(v_toFunctor_8428_);
                v___f_8437_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8437_, 0, v_toFunctor_8428_);
                v___f_8438_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8438_, 0, v_toFunctor_8428_);
                v___x_8439_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8439_, 0, v___f_8437_);
                lean_ctor_set(v___x_8439_, 1, v___f_8438_);
                v___f_8440_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8440_, 0, v_toSeqRight_8431_);
                v___f_8441_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8441_, 0, v_toSeqLeft_8430_);
                v___f_8442_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8442_, 0, v_toSeq_8429_);
                if v_isShared_8434_ == 0 {
                    lean_ctor_set(v___x_8433_, 4, v___f_8440_);
                    lean_ctor_set(v___x_8433_, 3, v___f_8441_);
                    lean_ctor_set(v___x_8433_, 2, v___f_8442_);
                    lean_ctor_set(v___x_8433_, 1, v___f_8435_);
                    lean_ctor_set(v___x_8433_, 0, v___x_8439_);
                    v___x_8444_ = v___x_8433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8506_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8506_, 0, v___x_8439_);
                    lean_ctor_set(v_reuseFailAlloc_8506_, 1, v___f_8435_);
                    lean_ctor_set(v_reuseFailAlloc_8506_, 2, v___f_8442_);
                    lean_ctor_set(v_reuseFailAlloc_8506_, 3, v___f_8441_);
                    lean_ctor_set(v_reuseFailAlloc_8506_, 4, v___f_8440_);
                    v___x_8444_ = v_reuseFailAlloc_8506_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8427_ == 0 {
                    lean_ctor_set(v___x_8426_, 1, v___f_8436_);
                    lean_ctor_set(v___x_8426_, 0, v___x_8444_);
                    v___x_8446_ = v___x_8426_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8505_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8505_, 0, v___x_8444_);
                    lean_ctor_set(v_reuseFailAlloc_8505_, 1, v___f_8436_);
                    v___x_8446_ = v_reuseFailAlloc_8505_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8447_ = l_StateRefT_x27_instMonad___redArg(v___x_8446_);
                v_toApplicative_8448_ = lean_ctor_get(v___x_8447_, 0);
                v_isSharedCheck_8503_ = (!lean_is_exclusive(v___x_8447_)) as u8;
                if v_isSharedCheck_8503_ == 0 {
                    v_unused_8504_ = lean_ctor_get(v___x_8447_, 1);
                    lean_dec(v_unused_8504_);
                    v___x_8450_ = v___x_8447_;
                    v_isShared_8451_ = v_isSharedCheck_8503_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_8448_);
                    lean_dec(v___x_8447_);
                    v___x_8450_ = lean_box(0);
                    v_isShared_8451_ = v_isSharedCheck_8503_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_8452_ = lean_ctor_get(v_toApplicative_8448_, 0);
                v_toSeq_8453_ = lean_ctor_get(v_toApplicative_8448_, 2);
                v_toSeqLeft_8454_ = lean_ctor_get(v_toApplicative_8448_, 3);
                v_toSeqRight_8455_ = lean_ctor_get(v_toApplicative_8448_, 4);
                v_isSharedCheck_8501_ = (!lean_is_exclusive(v_toApplicative_8448_)) as u8;
                if v_isSharedCheck_8501_ == 0 {
                    v_unused_8502_ = lean_ctor_get(v_toApplicative_8448_, 1);
                    lean_dec(v_unused_8502_);
                    v___x_8457_ = v_toApplicative_8448_;
                    v_isShared_8458_ = v_isSharedCheck_8501_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_8455_);
                    lean_inc(v_toSeqLeft_8454_);
                    lean_inc(v_toSeq_8453_);
                    lean_inc(v_toFunctor_8452_);
                    lean_dec(v_toApplicative_8448_);
                    v___x_8457_ = lean_box(0);
                    v_isShared_8458_ = v_isSharedCheck_8501_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_8459_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0;
                v___f_8460_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1;
                lean_inc_ref(v_toFunctor_8452_);
                v___f_8461_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8461_, 0, v_toFunctor_8452_);
                v___f_8462_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8462_, 0, v_toFunctor_8452_);
                v___x_8463_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8463_, 0, v___f_8461_);
                lean_ctor_set(v___x_8463_, 1, v___f_8462_);
                v___f_8464_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8464_, 0, v_toSeqRight_8455_);
                v___f_8465_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8465_, 0, v_toSeqLeft_8454_);
                v___f_8466_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8466_, 0, v_toSeq_8453_);
                if v_isShared_8458_ == 0 {
                    lean_ctor_set(v___x_8457_, 4, v___f_8464_);
                    lean_ctor_set(v___x_8457_, 3, v___f_8465_);
                    lean_ctor_set(v___x_8457_, 2, v___f_8466_);
                    lean_ctor_set(v___x_8457_, 1, v___f_8459_);
                    lean_ctor_set(v___x_8457_, 0, v___x_8463_);
                    v___x_8468_ = v___x_8457_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8500_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 0, v___x_8463_);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 1, v___f_8459_);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 2, v___f_8466_);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 3, v___f_8465_);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 4, v___f_8464_);
                    v___x_8468_ = v_reuseFailAlloc_8500_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_8451_ == 0 {
                    lean_ctor_set(v___x_8450_, 1, v___f_8460_);
                    lean_ctor_set(v___x_8450_, 0, v___x_8468_);
                    v___x_8470_ = v___x_8450_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8499_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8499_, 0, v___x_8468_);
                    lean_ctor_set(v_reuseFailAlloc_8499_, 1, v___f_8460_);
                    v___x_8470_ = v_reuseFailAlloc_8499_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8471_ = lean_array_get_size(v_acc_8416_);
                v___x_8472_ = lean_array_get_size(v_declInfos_8413_);
                v___x_8473_ = lean_nat_dec_lt(v___x_8471_, v___x_8472_);
                if v___x_8473_ == 0 {
                    lean_dec_ref(v___x_8470_);
                    lean_dec_ref(v_declInfos_8413_);
                    lean_inc(v___y_8420_);
                    lean_inc_ref(v___y_8419_);
                    lean_inc(v___y_8418_);
                    lean_inc_ref(v___y_8417_);
                    v___x_8474_ = lean_apply_6(
                        v_k_8414_,
                        v_acc_8416_,
                        v___y_8417_,
                        v___y_8418_,
                        v___y_8419_,
                        v___y_8420_,
                        lean_box(0),
                    );
                    return v___x_8474_;
                } else {
                    v___f_8475_ = lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    lean_closure_set(v___f_8475_, 0, v___x_8470_);
                    v___x_8476_ = lean_box(0);
                    v___x_8477_ = 0;
                    v___f_8478_ = lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_8478_, 0, v___f_8475_);
                    v___x_8479_ = lean_box((v___x_8477_) as usize);
                    v___x_8480_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8480_, 0, v___x_8479_);
                    lean_ctor_set(v___x_8480_, 1, v___f_8478_);
                    v___x_8481_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_8481_, 0, v___x_8476_);
                    lean_ctor_set(v___x_8481_, 1, v___x_8480_);
                    v___x_8482_ = lean_array_get(v___x_8481_, v_declInfos_8413_, v___x_8471_);
                    lean_dec_ref_known(v___x_8481_, 2);
                    v_snd_8483_ = lean_ctor_get(v___x_8482_, 1);
                    lean_inc(v_snd_8483_);
                    v_fst_8484_ = lean_ctor_get(v___x_8482_, 0);
                    lean_inc(v_fst_8484_);
                    lean_dec(v___x_8482_);
                    v_fst_8485_ = lean_ctor_get(v_snd_8483_, 0);
                    lean_inc(v_fst_8485_);
                    v_snd_8486_ = lean_ctor_get(v_snd_8483_, 1);
                    lean_inc(v_snd_8486_);
                    lean_dec(v_snd_8483_);
                    lean_inc(v___y_8420_);
                    lean_inc_ref(v___y_8419_);
                    lean_inc(v___y_8418_);
                    lean_inc_ref(v___y_8417_);
                    lean_inc_ref(v_acc_8416_);
                    v___x_8487_ = lean_apply_6(
                        v_snd_8486_,
                        v_acc_8416_,
                        v___y_8417_,
                        v___y_8418_,
                        v___y_8419_,
                        v___y_8420_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_8487_) == 0 {
                        v_a_8488_ = lean_ctor_get(v___x_8487_, 0);
                        lean_inc(v_a_8488_);
                        lean_dec_ref_known(v___x_8487_, 1);
                        v___x_8489_ = (lean_unbox(v_fst_8485_) as u8);
                        lean_dec(v_fst_8485_);
                        v___x_8490_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_8416_, v_declInfos_8413_, v_k_8414_, v_kind_8415_, v_fst_8484_, v___x_8489_, v_a_8488_, v_kind_8415_, v___y_8417_, v___y_8418_, v___y_8419_, v___y_8420_);
                        return v___x_8490_;
                    } else {
                        lean_dec(v_fst_8485_);
                        lean_dec(v_fst_8484_);
                        lean_dec_ref(v_acc_8416_);
                        lean_dec_ref(v_k_8414_);
                        lean_dec_ref(v_declInfos_8413_);
                        v_a_8491_ = lean_ctor_get(v___x_8487_, 0);
                        v_isSharedCheck_8498_ = (!lean_is_exclusive(v___x_8487_)) as u8;
                        if v_isSharedCheck_8498_ == 0 {
                            v___x_8493_ = v___x_8487_;
                            v_isShared_8494_ = v_isSharedCheck_8498_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_8491_);
                            lean_dec(v___x_8487_);
                            v___x_8493_ = lean_box(0);
                            v_isShared_8494_ = v_isSharedCheck_8498_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_8494_ == 0 {
                    v___x_8496_ = v___x_8493_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8497_, 0, v_a_8491_);
                    v___x_8496_ = v_reuseFailAlloc_8497_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___lam__0(
    mut v_acc_8511_: *mut LeanObject,
    mut v_declInfos_8512_: *mut LeanObject,
    mut v_k_8513_: *mut LeanObject,
    mut v_kind_8514_: u8,
    mut v_b_8515_: *mut LeanObject,
    mut v___y_8516_: *mut LeanObject,
    mut v___y_8517_: *mut LeanObject,
    mut v___y_8518_: *mut LeanObject,
    mut v___y_8519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8522_: *mut LeanObject = core::ptr::null_mut();
    v___x_8521_ = lean_array_push(v_acc_8511_, v_b_8515_);
    v___x_8522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_8512_, v_k_8513_, v_kind_8514_, v___x_8521_, v___y_8516_, v___y_8517_, v___y_8518_, v___y_8519_);
    return v___x_8522_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(
    mut v_acc_8523_: *mut LeanObject,
    mut v_declInfos_8524_: *mut LeanObject,
    mut v_k_8525_: *mut LeanObject,
    mut v_kind_8526_: *mut LeanObject,
    mut v_name_8527_: *mut LeanObject,
    mut v_bi_8528_: *mut LeanObject,
    mut v_type_8529_: *mut LeanObject,
    mut v_kind_8530_: *mut LeanObject,
    mut v___y_8531_: *mut LeanObject,
    mut v___y_8532_: *mut LeanObject,
    mut v___y_8533_: *mut LeanObject,
    mut v___y_8534_: *mut LeanObject,
    mut v___y_8535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8536_: u8 = 0;
    let mut v_bi_boxed_8537_: u8 = 0;
    let mut v_kind_boxed_8538_: u8 = 0;
    let mut v_res_8539_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8536_ = (lean_unbox(v_kind_8526_) as u8);
    v_bi_boxed_8537_ = (lean_unbox(v_bi_8528_) as u8);
    v_kind_boxed_8538_ = (lean_unbox(v_kind_8530_) as u8);
    v_res_8539_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_acc_8523_, v_declInfos_8524_, v_k_8525_, v_kind_boxed_8536_, v_name_8527_, v_bi_boxed_8537_, v_type_8529_, v_kind_boxed_8538_, v___y_8531_, v___y_8532_, v___y_8533_, v___y_8534_);
    lean_dec(v___y_8534_);
    lean_dec_ref(v___y_8533_);
    lean_dec(v___y_8532_);
    lean_dec_ref(v___y_8531_);
    return v_res_8539_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(
    mut v_declInfos_8540_: *mut LeanObject,
    mut v_k_8541_: *mut LeanObject,
    mut v_kind_8542_: *mut LeanObject,
    mut v_acc_8543_: *mut LeanObject,
    mut v___y_8544_: *mut LeanObject,
    mut v___y_8545_: *mut LeanObject,
    mut v___y_8546_: *mut LeanObject,
    mut v___y_8547_: *mut LeanObject,
    mut v___y_8548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8549_: u8 = 0;
    let mut v_res_8550_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8549_ = (lean_unbox(v_kind_8542_) as u8);
    v_res_8550_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_8540_, v_k_8541_, v_kind_boxed_8549_, v_acc_8543_, v___y_8544_, v___y_8545_, v___y_8546_, v___y_8547_);
    lean_dec(v___y_8547_);
    lean_dec_ref(v___y_8546_);
    lean_dec(v___y_8545_);
    lean_dec_ref(v___y_8544_);
    return v_res_8550_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(
    mut v_declInfos_8551_: *mut LeanObject,
    mut v_k_8552_: *mut LeanObject,
    mut v_kind_8553_: u8,
    mut v___y_8554_: *mut LeanObject,
    mut v___y_8555_: *mut LeanObject,
    mut v___y_8556_: *mut LeanObject,
    mut v___y_8557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8560_: *mut LeanObject = core::ptr::null_mut();
    v___x_8559_ =
        l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2;
    v___x_8560_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_declInfos_8551_, v_k_8552_, v_kind_8553_, v___x_8559_, v___y_8554_, v___y_8555_, v___y_8556_, v___y_8557_);
    return v___x_8560_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(
    mut v_declInfos_8561_: *mut LeanObject,
    mut v_k_8562_: *mut LeanObject,
    mut v_kind_8563_: *mut LeanObject,
    mut v___y_8564_: *mut LeanObject,
    mut v___y_8565_: *mut LeanObject,
    mut v___y_8566_: *mut LeanObject,
    mut v___y_8567_: *mut LeanObject,
    mut v___y_8568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8569_: u8 = 0;
    let mut v_res_8570_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8569_ = (lean_unbox(v_kind_8563_) as u8);
    v_res_8570_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_declInfos_8561_, v_k_8562_, v_kind_boxed_8569_, v___y_8564_, v___y_8565_, v___y_8566_, v___y_8567_);
    lean_dec(v___y_8567_);
    lean_dec_ref(v___y_8566_);
    lean_dec(v___y_8565_);
    lean_dec_ref(v___y_8564_);
    return v_res_8570_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(
    mut v_declInfos_8571_: *mut LeanObject,
    mut v_k_8572_: *mut LeanObject,
    mut v_kind_8573_: u8,
    mut v___y_8574_: *mut LeanObject,
    mut v___y_8575_: *mut LeanObject,
    mut v___y_8576_: *mut LeanObject,
    mut v___y_8577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_8579_: usize = 0;
    let mut v___x_8580_: usize = 0;
    let mut v___x_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8582_: *mut LeanObject = core::ptr::null_mut();
    v_sz_8579_ = lean_array_size(v_declInfos_8571_);
    v___x_8580_ = 0usize;
    v___x_8581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_8579_, v___x_8580_, v_declInfos_8571_);
    v___x_8582_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v___x_8581_, v_k_8572_, v_kind_8573_, v___y_8574_, v___y_8575_, v___y_8576_, v___y_8577_);
    return v___x_8582_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(
    mut v_declInfos_8583_: *mut LeanObject,
    mut v_k_8584_: *mut LeanObject,
    mut v_kind_8585_: *mut LeanObject,
    mut v___y_8586_: *mut LeanObject,
    mut v___y_8587_: *mut LeanObject,
    mut v___y_8588_: *mut LeanObject,
    mut v___y_8589_: *mut LeanObject,
    mut v___y_8590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_8591_: u8 = 0;
    let mut v_res_8592_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_8591_ = (lean_unbox(v_kind_8585_) as u8);
    v_res_8592_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_declInfos_8583_, v_k_8584_, v_kind_boxed_8591_, v___y_8586_, v___y_8587_, v___y_8588_, v___y_8589_);
    lean_dec(v___y_8589_);
    lean_dec_ref(v___y_8588_);
    lean_dec(v___y_8587_);
    lean_dec_ref(v___y_8586_);
    return v_res_8592_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(
    mut v_paramsIndices_8593_: *mut LeanObject,
    mut v_numParams_8594_: *mut LeanObject,
    mut v_a_8595_: *mut LeanObject,
    mut v___x_8596_: *mut LeanObject,
    mut v_compFields_8597_: *mut LeanObject,
    mut v_val_8598_: *mut LeanObject,
    mut v___y_8599_: *mut LeanObject,
    mut v___y_8600_: *mut LeanObject,
    mut v___y_8601_: *mut LeanObject,
    mut v___y_8602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_8609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_8610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8614_: usize = 0;
    let mut v___x_8615_: usize = 0;
    let mut v___x_8616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8617_: u8 = 0;
    let mut v___x_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8604_ = lean_unsigned_to_nat(0);
                lean_inc(v_numParams_8594_);
                lean_inc_ref(v_paramsIndices_8593_);
                v___x_8605_ = l_Array_toSubarray___redArg(
                    v_paramsIndices_8593_,
                    v___x_8604_,
                    v_numParams_8594_,
                );
                v___x_8606_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2;
                v___x_8607_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_8605_, v___x_8606_);
                v___x_8619_ = lean_array_get_size(v_paramsIndices_8593_);
                v___x_8620_ = lean_nat_dec_le(v_numParams_8594_, v___x_8604_);
                if v___x_8620_ == 0 {
                    v_lower_8609_ = v_numParams_8594_;
                    v_upper_8610_ = v___x_8619_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_numParams_8594_);
                    v_lower_8609_ = v___x_8604_;
                    v_upper_8610_ = v___x_8619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8611_ = l_Array_toSubarray___redArg(
                    v_paramsIndices_8593_,
                    v_lower_8609_,
                    v_upper_8610_,
                );
                v___x_8612_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_8611_, v___x_8606_);
                lean_inc_ref(v_val_8598_);
                lean_inc_ref(v___x_8612_);
                lean_inc_ref(v_compFields_8597_);
                lean_inc_ref(v___x_8607_);
                v___f_8613_ = lean_alloc_closure(
                    l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    6,
                );
                lean_closure_set(v___f_8613_, 0, v_a_8595_);
                lean_closure_set(v___f_8613_, 1, v___x_8596_);
                lean_closure_set(v___f_8613_, 2, v___x_8607_);
                lean_closure_set(v___f_8613_, 3, v_compFields_8597_);
                lean_closure_set(v___f_8613_, 4, v___x_8612_);
                lean_closure_set(v___f_8613_, 5, v_val_8598_);
                v_sz_8614_ = lean_array_size(v_compFields_8597_);
                v___x_8615_ = 0usize;
                v___x_8616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_8607_, v___x_8612_, v_val_8598_, v_sz_8614_, v___x_8615_, v_compFields_8597_);
                v___x_8617_ = 0;
                v___x_8618_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v___x_8616_, v___f_8613_, v___x_8617_, v___y_8599_, v___y_8600_, v___y_8601_, v___y_8602_);
                return v___x_8618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(
    mut v_paramsIndices_8621_: *mut LeanObject,
    mut v_numParams_8622_: *mut LeanObject,
    mut v_a_8623_: *mut LeanObject,
    mut v___x_8624_: *mut LeanObject,
    mut v_compFields_8625_: *mut LeanObject,
    mut v_val_8626_: *mut LeanObject,
    mut v___y_8627_: *mut LeanObject,
    mut v___y_8628_: *mut LeanObject,
    mut v___y_8629_: *mut LeanObject,
    mut v___y_8630_: *mut LeanObject,
    mut v___y_8631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8632_: *mut LeanObject = core::ptr::null_mut();
    v_res_8632_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(
        v_paramsIndices_8621_,
        v_numParams_8622_,
        v_a_8623_,
        v___x_8624_,
        v_compFields_8625_,
        v_val_8626_,
        v___y_8627_,
        v___y_8628_,
        v___y_8629_,
        v___y_8630_,
    );
    lean_dec(v___y_8630_);
    lean_dec_ref(v___y_8629_);
    lean_dec(v___y_8628_);
    lean_dec_ref(v___y_8627_);
    return v_res_8632_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(
    mut v_k_8633_: *mut LeanObject,
    mut v_b_8634_: *mut LeanObject,
    mut v___y_8635_: *mut LeanObject,
    mut v___y_8636_: *mut LeanObject,
    mut v___y_8637_: *mut LeanObject,
    mut v___y_8638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8640_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_8638_);
    lean_inc_ref(v___y_8637_);
    lean_inc(v___y_8636_);
    lean_inc_ref(v___y_8635_);
    v___x_8640_ = lean_apply_6(
        v_k_8633_,
        v_b_8634_,
        v___y_8635_,
        v___y_8636_,
        v___y_8637_,
        v___y_8638_,
        lean_box(0),
    );
    return v___x_8640_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(
    mut v_k_8641_: *mut LeanObject,
    mut v_b_8642_: *mut LeanObject,
    mut v___y_8643_: *mut LeanObject,
    mut v___y_8644_: *mut LeanObject,
    mut v___y_8645_: *mut LeanObject,
    mut v___y_8646_: *mut LeanObject,
    mut v___y_8647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8648_: *mut LeanObject = core::ptr::null_mut();
    v_res_8648_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_8641_, v_b_8642_, v___y_8643_, v___y_8644_, v___y_8645_, v___y_8646_);
    lean_dec(v___y_8646_);
    lean_dec_ref(v___y_8645_);
    lean_dec(v___y_8644_);
    lean_dec_ref(v___y_8643_);
    return v_res_8648_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(
    mut v_name_8649_: *mut LeanObject,
    mut v_bi_8650_: u8,
    mut v_type_8651_: *mut LeanObject,
    mut v_k_8652_: *mut LeanObject,
    mut v_kind_8653_: u8,
    mut v___y_8654_: *mut LeanObject,
    mut v___y_8655_: *mut LeanObject,
    mut v___y_8656_: *mut LeanObject,
    mut v___y_8657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8664_: u8 = 0;
    let mut v___x_8666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8668_: u8 = 0;
    let mut v_a_8669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8672_: u8 = 0;
    let mut v___x_8674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8659_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_8659_, 0, v_k_8652_);
                v___x_8660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_8649_,
                    v_bi_8650_,
                    v_type_8651_,
                    v___f_8659_,
                    v_kind_8653_,
                    v___y_8654_,
                    v___y_8655_,
                    v___y_8656_,
                    v___y_8657_,
                );
                if lean_obj_tag(v___x_8660_) == 0 {
                    v_a_8661_ = lean_ctor_get(v___x_8660_, 0);
                    v_isSharedCheck_8668_ = (!lean_is_exclusive(v___x_8660_)) as u8;
                    if v_isSharedCheck_8668_ == 0 {
                        v___x_8663_ = v___x_8660_;
                        v_isShared_8664_ = v_isSharedCheck_8668_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8661_);
                        lean_dec(v___x_8660_);
                        v___x_8663_ = lean_box(0);
                        v_isShared_8664_ = v_isSharedCheck_8668_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8669_ = lean_ctor_get(v___x_8660_, 0);
                    v_isSharedCheck_8676_ = (!lean_is_exclusive(v___x_8660_)) as u8;
                    if v_isSharedCheck_8676_ == 0 {
                        v___x_8671_ = v___x_8660_;
                        v_isShared_8672_ = v_isSharedCheck_8676_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8669_);
                        lean_dec(v___x_8660_);
                        v___x_8671_ = lean_box(0);
                        v_isShared_8672_ = v_isSharedCheck_8676_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8664_ == 0 {
                    v___x_8666_ = v___x_8663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8667_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8667_, 0, v_a_8661_);
                    v___x_8666_ = v_reuseFailAlloc_8667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8666_;
            }
            3 => {
                if v_isShared_8672_ == 0 {
                    v___x_8674_ = v___x_8671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8675_, 0, v_a_8669_);
                    v___x_8674_ = v_reuseFailAlloc_8675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(
    mut v_name_8677_: *mut LeanObject,
    mut v_bi_8678_: *mut LeanObject,
    mut v_type_8679_: *mut LeanObject,
    mut v_k_8680_: *mut LeanObject,
    mut v_kind_8681_: *mut LeanObject,
    mut v___y_8682_: *mut LeanObject,
    mut v___y_8683_: *mut LeanObject,
    mut v___y_8684_: *mut LeanObject,
    mut v___y_8685_: *mut LeanObject,
    mut v___y_8686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_8687_: u8 = 0;
    let mut v_kind_boxed_8688_: u8 = 0;
    let mut v_res_8689_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_8687_ = (lean_unbox(v_bi_8678_) as u8);
    v_kind_boxed_8688_ = (lean_unbox(v_kind_8681_) as u8);
    v_res_8689_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_8677_, v_bi_boxed_8687_, v_type_8679_, v_k_8680_, v_kind_boxed_8688_, v___y_8682_, v___y_8683_, v___y_8684_, v___y_8685_);
    lean_dec(v___y_8685_);
    lean_dec_ref(v___y_8684_);
    lean_dec(v___y_8683_);
    lean_dec_ref(v___y_8682_);
    return v_res_8689_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(
    mut v_name_8690_: *mut LeanObject,
    mut v_type_8691_: *mut LeanObject,
    mut v_k_8692_: *mut LeanObject,
    mut v___y_8693_: *mut LeanObject,
    mut v___y_8694_: *mut LeanObject,
    mut v___y_8695_: *mut LeanObject,
    mut v___y_8696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8698_: u8 = 0;
    let mut v___x_8699_: u8 = 0;
    let mut v___x_8700_: *mut LeanObject = core::ptr::null_mut();
    v___x_8698_ = 0;
    v___x_8699_ = 0;
    v___x_8700_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_8690_, v___x_8698_, v_type_8691_, v_k_8692_, v___x_8699_, v___y_8693_, v___y_8694_, v___y_8695_, v___y_8696_);
    return v___x_8700_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(
    mut v_name_8701_: *mut LeanObject,
    mut v_type_8702_: *mut LeanObject,
    mut v_k_8703_: *mut LeanObject,
    mut v___y_8704_: *mut LeanObject,
    mut v___y_8705_: *mut LeanObject,
    mut v___y_8706_: *mut LeanObject,
    mut v___y_8707_: *mut LeanObject,
    mut v___y_8708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8709_: *mut LeanObject = core::ptr::null_mut();
    v_res_8709_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_8701_, v_type_8702_, v_k_8703_, v___y_8704_, v___y_8705_, v___y_8706_, v___y_8707_);
    lean_dec(v___y_8707_);
    lean_dec_ref(v___y_8706_);
    lean_dec(v___y_8705_);
    lean_dec_ref(v___y_8704_);
    return v_res_8709_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(
    mut v_numParams_8710_: *mut LeanObject,
    mut v_a_8711_: *mut LeanObject,
    mut v___x_8712_: *mut LeanObject,
    mut v_compFields_8713_: *mut LeanObject,
    mut v_name_8714_: *mut LeanObject,
    mut v_paramsIndices_8715_: *mut LeanObject,
    mut v_x_8716_: *mut LeanObject,
    mut v___y_8717_: *mut LeanObject,
    mut v___y_8718_: *mut LeanObject,
    mut v___y_8719_: *mut LeanObject,
    mut v___y_8720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8726_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___x_8712_);
    lean_inc_ref(v_paramsIndices_8715_);
    v___f_8722_ = lean_alloc_closure(
        l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed
            as *mut core::ffi::c_void,
        11,
        5,
    );
    lean_closure_set(v___f_8722_, 0, v_paramsIndices_8715_);
    lean_closure_set(v___f_8722_, 1, v_numParams_8710_);
    lean_closure_set(v___f_8722_, 2, v_a_8711_);
    lean_closure_set(v___f_8722_, 3, v___x_8712_);
    lean_closure_set(v___f_8722_, 4, v_compFields_8713_);
    v___x_8723_ = l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1;
    v___x_8724_ = l_Lean_mkConst(v_name_8714_, v___x_8712_);
    v___x_8725_ = l_Lean_mkAppN(v___x_8724_, v_paramsIndices_8715_);
    lean_dec_ref(v_paramsIndices_8715_);
    v___x_8726_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_8723_, v___x_8725_, v___f_8722_, v___y_8717_, v___y_8718_, v___y_8719_, v___y_8720_);
    return v___x_8726_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(
    mut v_numParams_8727_: *mut LeanObject,
    mut v_a_8728_: *mut LeanObject,
    mut v___x_8729_: *mut LeanObject,
    mut v_compFields_8730_: *mut LeanObject,
    mut v_name_8731_: *mut LeanObject,
    mut v_paramsIndices_8732_: *mut LeanObject,
    mut v_x_8733_: *mut LeanObject,
    mut v___y_8734_: *mut LeanObject,
    mut v___y_8735_: *mut LeanObject,
    mut v___y_8736_: *mut LeanObject,
    mut v___y_8737_: *mut LeanObject,
    mut v___y_8738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8739_: *mut LeanObject = core::ptr::null_mut();
    v_res_8739_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(
        v_numParams_8727_,
        v_a_8728_,
        v___x_8729_,
        v_compFields_8730_,
        v_name_8731_,
        v_paramsIndices_8732_,
        v_x_8733_,
        v___y_8734_,
        v___y_8735_,
        v___y_8736_,
        v___y_8737_,
    );
    lean_dec(v___y_8737_);
    lean_dec_ref(v___y_8736_);
    lean_dec(v___y_8735_);
    lean_dec_ref(v___y_8734_);
    lean_dec_ref(v_x_8733_);
    return v_res_8739_;
}
pub unsafe fn _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1()
-> *mut LeanObject {
    let mut v___x_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut LeanObject = core::ptr::null_mut();
    v___x_8741_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0;
    v___x_8742_ = l_Lean_stringToMessageData(v___x_8741_);
    return v___x_8742_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(
    mut v_declName_8743_: *mut LeanObject,
    mut v_compFields_8744_: *mut LeanObject,
    mut v_a_8745_: *mut LeanObject,
    mut v_a_8746_: *mut LeanObject,
    mut v_a_8747_: *mut LeanObject,
    mut v_a_8748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_8752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_8754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_8760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8766_: u8 = 0;
    let mut v___x_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8770_: u8 = 0;
    let mut v___x_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8776_: u8 = 0;
    let mut v___x_8778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8750_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_8743_, v_a_8745_, v_a_8746_, v_a_8747_, v_a_8748_);
                if lean_obj_tag(v___x_8750_) == 0 {
                    v_a_8751_ = lean_ctor_get(v___x_8750_, 0);
                    lean_inc(v_a_8751_);
                    lean_dec_ref_known(v___x_8750_, 1);
                    v_toConstantVal_8752_ = lean_ctor_get(v_a_8751_, 0);
                    v_numParams_8753_ = lean_ctor_get(v_a_8751_, 1);
                    lean_inc(v_numParams_8753_);
                    v_ctors_8754_ = lean_ctor_get(v_a_8751_, 4);
                    v___x_8768_ = l_List_lengthTR___redArg(v_ctors_8754_);
                    v___x_8769_ = lean_unsigned_to_nat(2);
                    v___x_8770_ = lean_nat_dec_lt(v___x_8768_, v___x_8769_);
                    lean_dec(v___x_8768_);
                    if v___x_8770_ == 0 {
                        v___y_8756_ = v_a_8745_;
                        v___y_8757_ = v_a_8746_;
                        v___y_8758_ = v_a_8747_;
                        v___y_8759_ = v_a_8748_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_numParams_8753_);
                        lean_dec(v_a_8751_);
                        lean_dec_ref(v_compFields_8744_);
                        v___x_8771_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once), _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
                        v___x_8772_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_8771_, v_a_8745_, v_a_8746_, v_a_8747_, v_a_8748_);
                        return v___x_8772_;
                    }
                } else {
                    lean_dec_ref(v_compFields_8744_);
                    v_a_8773_ = lean_ctor_get(v___x_8750_, 0);
                    v_isSharedCheck_8780_ = (!lean_is_exclusive(v___x_8750_)) as u8;
                    if v_isSharedCheck_8780_ == 0 {
                        v___x_8775_ = v___x_8750_;
                        v_isShared_8776_ = v_isSharedCheck_8780_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8773_);
                        lean_dec(v___x_8750_);
                        v___x_8775_ = lean_box(0);
                        v_isShared_8776_ = v_isSharedCheck_8780_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_name_8760_ = lean_ctor_get(v_toConstantVal_8752_, 0);
                lean_inc(v_name_8760_);
                v_levelParams_8761_ = lean_ctor_get(v_toConstantVal_8752_, 1);
                v_type_8762_ = lean_ctor_get(v_toConstantVal_8752_, 2);
                lean_inc_ref(v_type_8762_);
                v___x_8763_ = lean_box(0);
                lean_inc(v_levelParams_8761_);
                v___x_8764_ =
                    l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(
                        v_levelParams_8761_,
                        v___x_8763_,
                    );
                v___f_8765_ = lean_alloc_closure(
                    l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed
                        as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___f_8765_, 0, v_numParams_8753_);
                lean_closure_set(v___f_8765_, 1, v_a_8751_);
                lean_closure_set(v___f_8765_, 2, v___x_8764_);
                lean_closure_set(v___f_8765_, 3, v_compFields_8744_);
                lean_closure_set(v___f_8765_, 4, v_name_8760_);
                v___x_8766_ = 0;
                v___x_8767_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_8762_, v___f_8765_, v___x_8766_, v___y_8756_, v___y_8757_, v___y_8758_, v___y_8759_);
                return v___x_8767_;
            }
            2 => {
                if v_isShared_8776_ == 0 {
                    v___x_8778_ = v___x_8775_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8779_, 0, v_a_8773_);
                    v___x_8778_ = v_reuseFailAlloc_8779_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(
    mut v_declName_8781_: *mut LeanObject,
    mut v_compFields_8782_: *mut LeanObject,
    mut v_a_8783_: *mut LeanObject,
    mut v_a_8784_: *mut LeanObject,
    mut v_a_8785_: *mut LeanObject,
    mut v_a_8786_: *mut LeanObject,
    mut v_a_8787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8788_: *mut LeanObject = core::ptr::null_mut();
    v_res_8788_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(
        v_declName_8781_,
        v_compFields_8782_,
        v_a_8783_,
        v_a_8784_,
        v_a_8785_,
        v_a_8786_,
    );
    lean_dec(v_a_8786_);
    lean_dec_ref(v_a_8785_);
    lean_dec(v_a_8784_);
    lean_dec_ref(v_a_8783_);
    return v_res_8788_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(
    mut v_00_u03b1_8789_: *mut LeanObject,
    mut v_name_8790_: *mut LeanObject,
    mut v_bi_8791_: u8,
    mut v_type_8792_: *mut LeanObject,
    mut v_k_8793_: *mut LeanObject,
    mut v_kind_8794_: u8,
    mut v___y_8795_: *mut LeanObject,
    mut v___y_8796_: *mut LeanObject,
    mut v___y_8797_: *mut LeanObject,
    mut v___y_8798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8800_: *mut LeanObject = core::ptr::null_mut();
    v___x_8800_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_8790_, v_bi_8791_, v_type_8792_, v_k_8793_, v_kind_8794_, v___y_8795_, v___y_8796_, v___y_8797_, v___y_8798_);
    return v___x_8800_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(
    mut v_00_u03b1_8801_: *mut LeanObject,
    mut v_name_8802_: *mut LeanObject,
    mut v_bi_8803_: *mut LeanObject,
    mut v_type_8804_: *mut LeanObject,
    mut v_k_8805_: *mut LeanObject,
    mut v_kind_8806_: *mut LeanObject,
    mut v___y_8807_: *mut LeanObject,
    mut v___y_8808_: *mut LeanObject,
    mut v___y_8809_: *mut LeanObject,
    mut v___y_8810_: *mut LeanObject,
    mut v___y_8811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_8812_: u8 = 0;
    let mut v_kind_boxed_8813_: u8 = 0;
    let mut v_res_8814_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_8812_ = (lean_unbox(v_bi_8803_) as u8);
    v_kind_boxed_8813_ = (lean_unbox(v_kind_8806_) as u8);
    v_res_8814_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_8801_, v_name_8802_, v_bi_boxed_8812_, v_type_8804_, v_k_8805_, v_kind_boxed_8813_, v___y_8807_, v___y_8808_, v___y_8809_, v___y_8810_);
    lean_dec(v___y_8810_);
    lean_dec_ref(v___y_8809_);
    lean_dec(v___y_8808_);
    lean_dec_ref(v___y_8807_);
    return v_res_8814_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(
    mut v_00_u03b1_8815_: *mut LeanObject,
    mut v_name_8816_: *mut LeanObject,
    mut v_type_8817_: *mut LeanObject,
    mut v_k_8818_: *mut LeanObject,
    mut v___y_8819_: *mut LeanObject,
    mut v___y_8820_: *mut LeanObject,
    mut v___y_8821_: *mut LeanObject,
    mut v___y_8822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8824_: *mut LeanObject = core::ptr::null_mut();
    v___x_8824_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_8816_, v_type_8817_, v_k_8818_, v___y_8819_, v___y_8820_, v___y_8821_, v___y_8822_);
    return v___x_8824_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(
    mut v_00_u03b1_8825_: *mut LeanObject,
    mut v_name_8826_: *mut LeanObject,
    mut v_type_8827_: *mut LeanObject,
    mut v_k_8828_: *mut LeanObject,
    mut v___y_8829_: *mut LeanObject,
    mut v___y_8830_: *mut LeanObject,
    mut v___y_8831_: *mut LeanObject,
    mut v___y_8832_: *mut LeanObject,
    mut v___y_8833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8834_: *mut LeanObject = core::ptr::null_mut();
    v_res_8834_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_8825_, v_name_8826_, v_type_8827_, v_k_8828_, v___y_8829_, v___y_8830_, v___y_8831_, v___y_8832_);
    lean_dec(v___y_8832_);
    lean_dec_ref(v___y_8831_);
    lean_dec(v___y_8830_);
    lean_dec_ref(v___y_8829_);
    return v_res_8834_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(
    mut v_as_8835_: *mut LeanObject,
    mut v_sz_8836_: usize,
    mut v_i_8837_: usize,
    mut v_b_8838_: *mut LeanObject,
    mut v___y_8839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8843_: usize = 0;
    let mut v___x_8844_: usize = 0;
    let mut v___x_8846_: u8 = 0;
    let mut v___x_8847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8851_: u8 = 0;
    let mut v___x_8852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8854_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8846_ = lean_usize_dec_lt(v_i_8837_, v_sz_8836_);
                if v___x_8846_ == 0 {
                    v___x_8847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8847_, 0, v_b_8838_);
                    return v___x_8847_;
                } else {
                    v___x_8848_ = lean_st_ref_get(v___y_8839_);
                    v_env_8849_ = lean_ctor_get(v___x_8848_, 0);
                    lean_inc_ref(v_env_8849_);
                    lean_dec(v___x_8848_);
                    v_a_8850_ = lean_array_uget_borrowed(v_as_8835_, v_i_8837_);
                    lean_inc(v_a_8850_);
                    v___x_8851_ = l_Lean_isExtern(v_env_8849_, v_a_8850_);
                    if v___x_8851_ == 0 {
                        v___x_8852_ = l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                        lean_inc(v_a_8850_);
                        v___x_8853_ = l_Lean_Name_append(v_a_8850_, v___x_8852_);
                        v___x_8854_ = lean_array_push(v_b_8838_, v___x_8853_);
                        v_a_8842_ = v___x_8854_;
                        state = 1;
                        continue;
                    } else {
                        v_a_8842_ = v_b_8838_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8843_ = 1usize;
                v___x_8844_ = lean_usize_add(v_i_8837_, v___x_8843_);
                v_i_8837_ = v___x_8844_;
                v_b_8838_ = v_a_8842_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(
    mut v_as_8855_: *mut LeanObject,
    mut v_sz_8856_: *mut LeanObject,
    mut v_i_8857_: *mut LeanObject,
    mut v_b_8858_: *mut LeanObject,
    mut v___y_8859_: *mut LeanObject,
    mut v___y_8860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8861_: usize = 0;
    let mut v_i_boxed_8862_: usize = 0;
    let mut v_res_8863_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8861_ = lean_unbox_usize(v_sz_8856_);
    lean_dec(v_sz_8856_);
    v_i_boxed_8862_ = lean_unbox_usize(v_i_8857_);
    lean_dec(v_i_8857_);
    v_res_8863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_8855_, v_sz_boxed_8861_, v_i_boxed_8862_, v_b_8858_, v___y_8859_);
    lean_dec(v___y_8859_);
    lean_dec_ref(v_as_8855_);
    return v_res_8863_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(
    mut v_as_x27_8864_: *mut LeanObject,
    mut v_b_8865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_8864_) == 0 {
                    v___x_8867_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8867_, 0, v_b_8865_);
                    return v___x_8867_;
                } else {
                    v_head_8868_ = lean_ctor_get(v_as_x27_8864_, 0);
                    v_tail_8869_ = lean_ctor_get(v_as_x27_8864_, 1);
                    v___x_8870_ = l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                    lean_inc(v_head_8868_);
                    v___x_8871_ = l_Lean_Name_append(v_head_8868_, v___x_8870_);
                    v___x_8872_ = lean_array_push(v_b_8865_, v___x_8871_);
                    v_as_x27_8864_ = v_tail_8869_;
                    v_b_8865_ = v___x_8872_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(
    mut v_as_x27_8874_: *mut LeanObject,
    mut v_b_8875_: *mut LeanObject,
    mut v___y_8876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8877_: *mut LeanObject = core::ptr::null_mut();
    v_res_8877_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(
            v_as_x27_8874_,
            v_b_8875_,
        );
    lean_dec(v_as_x27_8874_);
    return v_res_8877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(
    mut v_as_8878_: *mut LeanObject,
    mut v_sz_8879_: usize,
    mut v_i_8880_: usize,
    mut v_b_8881_: *mut LeanObject,
    mut v___y_8882_: *mut LeanObject,
    mut v___y_8883_: *mut LeanObject,
    mut v___y_8884_: *mut LeanObject,
    mut v___y_8885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8887_: u8 = 0;
    let mut v___x_8888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_8894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8897_: usize = 0;
    let mut v___x_8898_: usize = 0;
    let mut v___x_8899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8901_: usize = 0;
    let mut v___x_8902_: usize = 0;
    let mut v_a_8904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8907_: u8 = 0;
    let mut v___x_8909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8887_ = lean_usize_dec_lt(v_i_8880_, v_sz_8879_);
                if v___x_8887_ == 0 {
                    v___x_8888_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8888_, 0, v_b_8881_);
                    return v___x_8888_;
                } else {
                    v_a_8889_ = lean_array_uget_borrowed(v_as_8878_, v_i_8880_);
                    v_fst_8890_ = lean_ctor_get(v_a_8889_, 0);
                    v_snd_8891_ = lean_ctor_get(v_a_8889_, 1);
                    lean_inc(v_fst_8890_);
                    v___x_8892_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_8890_, v___y_8882_, v___y_8883_, v___y_8884_, v___y_8885_);
                    if lean_obj_tag(v___x_8892_) == 0 {
                        v_a_8893_ = lean_ctor_get(v___x_8892_, 0);
                        lean_inc(v_a_8893_);
                        lean_dec_ref_known(v___x_8892_, 1);
                        v_ctors_8894_ = lean_ctor_get(v_a_8893_, 4);
                        lean_inc(v_ctors_8894_);
                        lean_dec(v_a_8893_);
                        v___x_8895_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_8894_, v_b_8881_);
                        lean_dec(v_ctors_8894_);
                        if lean_obj_tag(v___x_8895_) == 0 {
                            v_a_8896_ = lean_ctor_get(v___x_8895_, 0);
                            lean_inc(v_a_8896_);
                            lean_dec_ref_known(v___x_8895_, 1);
                            v_sz_8897_ = lean_array_size(v_snd_8891_);
                            v___x_8898_ = 0usize;
                            v___x_8899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_8891_, v_sz_8897_, v___x_8898_, v_a_8896_, v___y_8885_);
                            if lean_obj_tag(v___x_8899_) == 0 {
                                v_a_8900_ = lean_ctor_get(v___x_8899_, 0);
                                lean_inc(v_a_8900_);
                                lean_dec_ref_known(v___x_8899_, 1);
                                v___x_8901_ = 1usize;
                                v___x_8902_ = lean_usize_add(v_i_8880_, v___x_8901_);
                                v_i_8880_ = v___x_8902_;
                                v_b_8881_ = v_a_8900_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_8899_;
                            }
                        } else {
                            return v___x_8895_;
                        }
                    } else {
                        lean_dec_ref(v_b_8881_);
                        v_a_8904_ = lean_ctor_get(v___x_8892_, 0);
                        v_isSharedCheck_8911_ = (!lean_is_exclusive(v___x_8892_)) as u8;
                        if v_isSharedCheck_8911_ == 0 {
                            v___x_8906_ = v___x_8892_;
                            v_isShared_8907_ = v_isSharedCheck_8911_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8904_);
                            lean_dec(v___x_8892_);
                            v___x_8906_ = lean_box(0);
                            v_isShared_8907_ = v_isSharedCheck_8911_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8907_ == 0 {
                    v___x_8909_ = v___x_8906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8910_, 0, v_a_8904_);
                    v___x_8909_ = v_reuseFailAlloc_8910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(
    mut v_as_8912_: *mut LeanObject,
    mut v_sz_8913_: *mut LeanObject,
    mut v_i_8914_: *mut LeanObject,
    mut v_b_8915_: *mut LeanObject,
    mut v___y_8916_: *mut LeanObject,
    mut v___y_8917_: *mut LeanObject,
    mut v___y_8918_: *mut LeanObject,
    mut v___y_8919_: *mut LeanObject,
    mut v___y_8920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_8921_: usize = 0;
    let mut v_i_boxed_8922_: usize = 0;
    let mut v_res_8923_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_8921_ = lean_unbox_usize(v_sz_8913_);
    lean_dec(v_sz_8913_);
    v_i_boxed_8922_ = lean_unbox_usize(v_i_8914_);
    lean_dec(v_i_8914_);
    v_res_8923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_8912_, v_sz_boxed_8921_, v_i_boxed_8922_, v_b_8915_, v___y_8916_, v___y_8917_, v___y_8918_, v___y_8919_);
    lean_dec(v___y_8919_);
    lean_dec_ref(v___y_8918_);
    lean_dec(v___y_8917_);
    lean_dec_ref(v___y_8916_);
    lean_dec_ref(v_as_8912_);
    return v_res_8923_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(
    mut v___y_8931_: u8,
    mut v_suppressElabErrors_8932_: u8,
    mut v_x_8933_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_8933_) == 1 {
        let mut v_pre_8934_: *mut LeanObject = core::ptr::null_mut();
        v_pre_8934_ = lean_ctor_get(v_x_8933_, 0);
        match lean_obj_tag(v_pre_8934_) {
            1 => {
                let mut v_pre_8935_: *mut LeanObject = core::ptr::null_mut();
                v_pre_8935_ = lean_ctor_get(v_pre_8934_, 0);
                match lean_obj_tag(v_pre_8935_) {
                    0 => {
                        let mut v_str_8936_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_8937_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_8938_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_8939_: u8 = 0;
                        v_str_8936_ = lean_ctor_get(v_x_8933_, 1);
                        v_str_8937_ = lean_ctor_get(v_pre_8934_, 1);
                        v___x_8938_ = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
                        v___x_8939_ = lean_string_dec_eq(v_str_8937_, v___x_8938_);
                        if v___x_8939_ == 0 {
                            let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_8941_: u8 = 0;
                            v___x_8940_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0;
                            v___x_8941_ = lean_string_dec_eq(v_str_8937_, v___x_8940_);
                            if v___x_8941_ == 0 {
                                return v___y_8931_;
                            } else {
                                let mut v___x_8942_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_8943_: u8 = 0;
                                v___x_8942_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1;
                                v___x_8943_ = lean_string_dec_eq(v_str_8936_, v___x_8942_);
                                if v___x_8943_ == 0 {
                                    return v___y_8931_;
                                } else {
                                    return v_suppressElabErrors_8932_;
                                }
                            }
                        } else {
                            let mut v___x_8944_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_8945_: u8 = 0;
                            v___x_8944_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2;
                            v___x_8945_ = lean_string_dec_eq(v_str_8936_, v___x_8944_);
                            if v___x_8945_ == 0 {
                                return v___y_8931_;
                            } else {
                                return v_suppressElabErrors_8932_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_8946_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_8946_ = lean_ctor_get(v_pre_8935_, 0);
                        if lean_obj_tag(v_pre_8946_) == 0 {
                            let mut v_str_8947_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_8948_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_8949_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_8950_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_8951_: u8 = 0;
                            v_str_8947_ = lean_ctor_get(v_x_8933_, 1);
                            v_str_8948_ = lean_ctor_get(v_pre_8934_, 1);
                            v_str_8949_ = lean_ctor_get(v_pre_8935_, 1);
                            v___x_8950_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3;
                            v___x_8951_ = lean_string_dec_eq(v_str_8949_, v___x_8950_);
                            if v___x_8951_ == 0 {
                                return v___y_8931_;
                            } else {
                                let mut v___x_8952_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_8953_: u8 = 0;
                                v___x_8952_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4;
                                v___x_8953_ = lean_string_dec_eq(v_str_8948_, v___x_8952_);
                                if v___x_8953_ == 0 {
                                    return v___y_8931_;
                                } else {
                                    let mut v___x_8954_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_8955_: u8 = 0;
                                    v___x_8954_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5;
                                    v___x_8955_ = lean_string_dec_eq(v_str_8947_, v___x_8954_);
                                    if v___x_8955_ == 0 {
                                        return v___y_8931_;
                                    } else {
                                        return v_suppressElabErrors_8932_;
                                    }
                                }
                            }
                        } else {
                            return v___y_8931_;
                        }
                    }
                    _ => {
                        return v___y_8931_;
                    }
                }
            }
            0 => {
                let mut v_str_8956_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8957_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_8958_: u8 = 0;
                v_str_8956_ = lean_ctor_get(v_x_8933_, 1);
                v___x_8957_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6;
                v___x_8958_ = lean_string_dec_eq(v_str_8956_, v___x_8957_);
                if v___x_8958_ == 0 {
                    return v___y_8931_;
                } else {
                    return v_suppressElabErrors_8932_;
                }
            }
            _ => {
                return v___y_8931_;
            }
        }
    } else {
        return v___y_8931_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(
    mut v___y_8959_: *mut LeanObject,
    mut v_suppressElabErrors_8960_: *mut LeanObject,
    mut v_x_8961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7410__boxed_8962_: u8 = 0;
    let mut v_suppressElabErrors_boxed_8963_: u8 = 0;
    let mut v_res_8964_: u8 = 0;
    let mut v_r_8965_: *mut LeanObject = core::ptr::null_mut();
    v___y_7410__boxed_8962_ = (lean_unbox(v___y_8959_) as u8);
    v_suppressElabErrors_boxed_8963_ = (lean_unbox(v_suppressElabErrors_8960_) as u8);
    v_res_8964_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7410__boxed_8962_, v_suppressElabErrors_boxed_8963_, v_x_8961_);
    lean_dec(v_x_8961_);
    v_r_8965_ = lean_box((v_res_8964_) as usize);
    return v_r_8965_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(
    mut v_opts_8966_: *mut LeanObject,
    mut v_opt_8967_: *mut LeanObject,
) -> u8 {
    let mut v_name_8968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_8969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_8970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8971_: *mut LeanObject = core::ptr::null_mut();
    v_name_8968_ = lean_ctor_get(v_opt_8967_, 0);
    v_defValue_8969_ = lean_ctor_get(v_opt_8967_, 1);
    v_map_8970_ = lean_ctor_get(v_opts_8966_, 0);
    v___x_8971_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_8970_,
            v_name_8968_,
        );
    if lean_obj_tag(v___x_8971_) == 0 {
        let mut v___x_8972_: u8 = 0;
        v___x_8972_ = (lean_unbox(v_defValue_8969_) as u8);
        return v___x_8972_;
    } else {
        let mut v_val_8973_: *mut LeanObject = core::ptr::null_mut();
        v_val_8973_ = lean_ctor_get(v___x_8971_, 0);
        lean_inc(v_val_8973_);
        lean_dec_ref_known(v___x_8971_, 1);
        if lean_obj_tag(v_val_8973_) == 1 {
            let mut v_v_8974_: u8 = 0;
            v_v_8974_ = lean_ctor_get_uint8(v_val_8973_, 0 as u32);
            lean_dec_ref_known(v_val_8973_, 0);
            return v_v_8974_;
        } else {
            let mut v___x_8975_: u8 = 0;
            lean_dec(v_val_8973_);
            v___x_8975_ = (lean_unbox(v_defValue_8969_) as u8);
            return v___x_8975_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(
    mut v_opts_8976_: *mut LeanObject,
    mut v_opt_8977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8978_: u8 = 0;
    let mut v_r_8979_: *mut LeanObject = core::ptr::null_mut();
    v_res_8978_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_8976_, v_opt_8977_);
    lean_dec_ref(v_opt_8977_);
    lean_dec_ref(v_opts_8976_);
    v_r_8979_ = lean_box((v_res_8978_) as usize);
    return v_r_8979_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(
    mut v_ref_8981_: *mut LeanObject,
    mut v_msgData_8982_: *mut LeanObject,
    mut v_severity_8983_: u8,
    mut v_isSilent_8984_: u8,
    mut v___y_8985_: *mut LeanObject,
    mut v___y_8986_: *mut LeanObject,
    mut v___y_8987_: *mut LeanObject,
    mut v___y_8988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8993_: u8 = 0;
    let mut v___y_8994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8995_: u8 = 0;
    let mut v___y_8996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_9001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_9002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_9004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_9005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_9006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_9007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_9008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_9009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_9010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_9011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9014_: u8 = 0;
    let mut v___x_9015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9025_: u8 = 0;
    let mut v___y_9027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9029_: u8 = 0;
    let mut v___y_9030_: u8 = 0;
    let mut v___y_9031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9032_: u8 = 0;
    let mut v___y_9033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9040_: u8 = 0;
    let mut v___x_9041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9045_: u8 = 0;
    let mut v___x_9046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9050_: u8 = 0;
    let mut v___y_9052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9054_: u8 = 0;
    let mut v___y_9055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9056_: u8 = 0;
    let mut v___y_9057_: u8 = 0;
    let mut v___y_9058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9065_: u8 = 0;
    let mut v___y_9066_: u8 = 0;
    let mut v___y_9067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9069_: u8 = 0;
    let mut v_ref_9070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9074_: u8 = 0;
    let mut v___y_9076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9078_: u8 = 0;
    let mut v___y_9079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9081_: u8 = 0;
    let mut v___y_9082_: u8 = 0;
    let mut v___y_9084_: u8 = 0;
    let mut v_fileName_9085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_9086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_9087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_9088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_9089_: u8 = 0;
    let mut v___x_9090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9093_: u8 = 0;
    let mut v___x_9094_: u8 = 0;
    let mut v___x_9095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9096_: u8 = 0;
    let mut v___x_9097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9099_: u8 = 0;
    let mut v___x_9100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9074_ = 2;
                v___x_9099_ = l_Lean_instBEqMessageSeverity_beq(v_severity_8983_, v___x_9074_);
                if v___x_9099_ == 0 {
                    v___y_9084_ = v___x_9099_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_8982_);
                    v___x_9100_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_8982_);
                    v___y_9084_ = v___x_9100_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_9000_ = lean_st_ref_take(v___y_8999_);
                v_currNamespace_9001_ = lean_ctor_get(v___y_8998_, 6);
                v_openDecls_9002_ = lean_ctor_get(v___y_8998_, 7);
                v_env_9003_ = lean_ctor_get(v___x_9000_, 0);
                v_nextMacroScope_9004_ = lean_ctor_get(v___x_9000_, 1);
                v_ngen_9005_ = lean_ctor_get(v___x_9000_, 2);
                v_auxDeclNGen_9006_ = lean_ctor_get(v___x_9000_, 3);
                v_traceState_9007_ = lean_ctor_get(v___x_9000_, 4);
                v_cache_9008_ = lean_ctor_get(v___x_9000_, 5);
                v_messages_9009_ = lean_ctor_get(v___x_9000_, 6);
                v_infoState_9010_ = lean_ctor_get(v___x_9000_, 7);
                v_snapshotTasks_9011_ = lean_ctor_get(v___x_9000_, 8);
                v_isSharedCheck_9025_ = (!lean_is_exclusive(v___x_9000_)) as u8;
                if v_isSharedCheck_9025_ == 0 {
                    v___x_9013_ = v___x_9000_;
                    v_isShared_9014_ = v_isSharedCheck_9025_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_9011_);
                    lean_inc(v_infoState_9010_);
                    lean_inc(v_messages_9009_);
                    lean_inc(v_cache_9008_);
                    lean_inc(v_traceState_9007_);
                    lean_inc(v_auxDeclNGen_9006_);
                    lean_inc(v_ngen_9005_);
                    lean_inc(v_nextMacroScope_9004_);
                    lean_inc(v_env_9003_);
                    lean_dec(v___x_9000_);
                    v___x_9013_ = lean_box(0);
                    v_isShared_9014_ = v_isSharedCheck_9025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_9002_);
                lean_inc(v_currNamespace_9001_);
                v___x_9015_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_9015_, 0, v_currNamespace_9001_);
                lean_ctor_set(v___x_9015_, 1, v_openDecls_9002_);
                v___x_9016_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_9016_, 0, v___x_9015_);
                lean_ctor_set(v___x_9016_, 1, v___y_8992_);
                lean_inc_ref(v___y_8997_);
                lean_inc_ref(v___y_8991_);
                v___x_9017_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_9017_, 0, v___y_8991_);
                lean_ctor_set(v___x_9017_, 1, v___y_8996_);
                lean_ctor_set(v___x_9017_, 2, v___y_8994_);
                lean_ctor_set(v___x_9017_, 3, v___y_8997_);
                lean_ctor_set(v___x_9017_, 4, v___x_9016_);
                lean_ctor_set_uint8(
                    v___x_9017_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_8995_,
                );
                lean_ctor_set_uint8(
                    v___x_9017_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_8993_,
                );
                lean_ctor_set_uint8(
                    v___x_9017_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_8984_,
                );
                v___x_9018_ = l_Lean_MessageLog_add(v___x_9017_, v_messages_9009_);
                if v_isShared_9014_ == 0 {
                    lean_ctor_set(v___x_9013_, 6, v___x_9018_);
                    v___x_9020_ = v___x_9013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9024_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 0, v_env_9003_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 1, v_nextMacroScope_9004_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 2, v_ngen_9005_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 3, v_auxDeclNGen_9006_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 4, v_traceState_9007_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 5, v_cache_9008_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 6, v___x_9018_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 7, v_infoState_9010_);
                    lean_ctor_set(v_reuseFailAlloc_9024_, 8, v_snapshotTasks_9011_);
                    v___x_9020_ = v_reuseFailAlloc_9024_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9021_ = lean_st_ref_set(v___y_8999_, v___x_9020_);
                v___x_9022_ = lean_box(0);
                v___x_9023_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9023_, 0, v___x_9022_);
                return v___x_9023_;
            }
            4 => {
                v___x_9035_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_8982_,
                    );
                v___x_9036_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_9035_, v___y_8985_, v___y_8986_, v___y_8987_, v___y_8988_);
                v_a_9037_ = lean_ctor_get(v___x_9036_, 0);
                v_isSharedCheck_9050_ = (!lean_is_exclusive(v___x_9036_)) as u8;
                if v_isSharedCheck_9050_ == 0 {
                    v___x_9039_ = v___x_9036_;
                    v_isShared_9040_ = v_isSharedCheck_9050_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_9037_);
                    lean_dec(v___x_9036_);
                    v___x_9039_ = lean_box(0);
                    v_isShared_9040_ = v_isSharedCheck_9050_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_9033_, 2);
                v___x_9041_ = l_Lean_FileMap_toPosition(v___y_9033_, v___y_9031_);
                lean_dec(v___y_9031_);
                v___x_9042_ = l_Lean_FileMap_toPosition(v___y_9033_, v___y_9034_);
                lean_dec(v___y_9034_);
                v___x_9043_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9043_, 0, v___x_9042_);
                v___x_9044_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0;
                if v___y_9032_ == 0 {
                    lean_del_object(v___x_9039_);
                    lean_dec_ref(v___y_9027_);
                    v___y_8991_ = v___y_9028_;
                    v___y_8992_ = v_a_9037_;
                    v___y_8993_ = v___y_9029_;
                    v___y_8994_ = v___x_9043_;
                    v___y_8995_ = v___y_9030_;
                    v___y_8996_ = v___x_9041_;
                    v___y_8997_ = v___x_9044_;
                    v___y_8998_ = v___y_8987_;
                    v___y_8999_ = v___y_8988_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_9037_);
                    v___x_9045_ = l_Lean_MessageData_hasTag(v___y_9027_, v_a_9037_);
                    if v___x_9045_ == 0 {
                        lean_dec_ref_known(v___x_9043_, 1);
                        lean_dec_ref(v___x_9041_);
                        lean_dec(v_a_9037_);
                        v___x_9046_ = lean_box(0);
                        if v_isShared_9040_ == 0 {
                            lean_ctor_set(v___x_9039_, 0, v___x_9046_);
                            v___x_9048_ = v___x_9039_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_9049_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_9049_, 0, v___x_9046_);
                            v___x_9048_ = v_reuseFailAlloc_9049_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_9039_);
                        v___y_8991_ = v___y_9028_;
                        v___y_8992_ = v_a_9037_;
                        v___y_8993_ = v___y_9029_;
                        v___y_8994_ = v___x_9043_;
                        v___y_8995_ = v___y_9030_;
                        v___y_8996_ = v___x_9041_;
                        v___y_8997_ = v___x_9044_;
                        v___y_8998_ = v___y_8987_;
                        v___y_8999_ = v___y_8988_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_9048_;
            }
            7 => {
                v___x_9060_ = l_Lean_Syntax_getTailPos_x3f(v___y_9055_, v___y_9056_);
                lean_dec(v___y_9055_);
                if lean_obj_tag(v___x_9060_) == 0 {
                    lean_inc(v___y_9059_);
                    v___y_9027_ = v___y_9052_;
                    v___y_9028_ = v___y_9053_;
                    v___y_9029_ = v___y_9054_;
                    v___y_9030_ = v___y_9056_;
                    v___y_9031_ = v___y_9059_;
                    v___y_9032_ = v___y_9057_;
                    v___y_9033_ = v___y_9058_;
                    v___y_9034_ = v___y_9059_;
                    state = 4;
                    continue;
                } else {
                    v_val_9061_ = lean_ctor_get(v___x_9060_, 0);
                    lean_inc(v_val_9061_);
                    lean_dec_ref_known(v___x_9060_, 1);
                    v___y_9027_ = v___y_9052_;
                    v___y_9028_ = v___y_9053_;
                    v___y_9029_ = v___y_9054_;
                    v___y_9030_ = v___y_9056_;
                    v___y_9031_ = v___y_9059_;
                    v___y_9032_ = v___y_9057_;
                    v___y_9033_ = v___y_9058_;
                    v___y_9034_ = v_val_9061_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_9070_ = l_Lean_replaceRef(v_ref_8981_, v___y_9068_);
                v___x_9071_ = l_Lean_Syntax_getPos_x3f(v_ref_9070_, v___y_9065_);
                if lean_obj_tag(v___x_9071_) == 0 {
                    v___x_9072_ = lean_unsigned_to_nat(0);
                    v___y_9052_ = v___y_9063_;
                    v___y_9053_ = v___y_9064_;
                    v___y_9054_ = v___y_9069_;
                    v___y_9055_ = v_ref_9070_;
                    v___y_9056_ = v___y_9065_;
                    v___y_9057_ = v___y_9066_;
                    v___y_9058_ = v___y_9067_;
                    v___y_9059_ = v___x_9072_;
                    state = 7;
                    continue;
                } else {
                    v_val_9073_ = lean_ctor_get(v___x_9071_, 0);
                    lean_inc(v_val_9073_);
                    lean_dec_ref_known(v___x_9071_, 1);
                    v___y_9052_ = v___y_9063_;
                    v___y_9053_ = v___y_9064_;
                    v___y_9054_ = v___y_9069_;
                    v___y_9055_ = v_ref_9070_;
                    v___y_9056_ = v___y_9065_;
                    v___y_9057_ = v___y_9066_;
                    v___y_9058_ = v___y_9067_;
                    v___y_9059_ = v_val_9073_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_9082_ == 0 {
                    v___y_9063_ = v___y_9077_;
                    v___y_9064_ = v___y_9076_;
                    v___y_9065_ = v___y_9081_;
                    v___y_9066_ = v___y_9078_;
                    v___y_9067_ = v___y_9079_;
                    v___y_9068_ = v___y_9080_;
                    v___y_9069_ = v_severity_8983_;
                    state = 8;
                    continue;
                } else {
                    v___y_9063_ = v___y_9077_;
                    v___y_9064_ = v___y_9076_;
                    v___y_9065_ = v___y_9081_;
                    v___y_9066_ = v___y_9078_;
                    v___y_9067_ = v___y_9079_;
                    v___y_9068_ = v___y_9080_;
                    v___y_9069_ = v___x_9074_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_9084_ == 0 {
                    v_fileName_9085_ = lean_ctor_get(v___y_8987_, 0);
                    v_fileMap_9086_ = lean_ctor_get(v___y_8987_, 1);
                    v_options_9087_ = lean_ctor_get(v___y_8987_, 2);
                    v_ref_9088_ = lean_ctor_get(v___y_8987_, 5);
                    v_suppressElabErrors_9089_ = lean_ctor_get_uint8(
                        v___y_8987_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_9090_ = lean_box((v___y_9084_) as usize);
                    v___x_9091_ = lean_box((v_suppressElabErrors_9089_) as usize);
                    v___f_9092_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_9092_, 0, v___x_9090_);
                    lean_closure_set(v___f_9092_, 1, v___x_9091_);
                    v___x_9093_ = 1;
                    v___x_9094_ = l_Lean_instBEqMessageSeverity_beq(v_severity_8983_, v___x_9093_);
                    if v___x_9094_ == 0 {
                        v___y_9076_ = v_fileName_9085_;
                        v___y_9077_ = v___f_9092_;
                        v___y_9078_ = v_suppressElabErrors_9089_;
                        v___y_9079_ = v_fileMap_9086_;
                        v___y_9080_ = v_ref_9088_;
                        v___y_9081_ = v___y_9084_;
                        v___y_9082_ = v___x_9094_;
                        state = 9;
                        continue;
                    } else {
                        v___x_9095_ = l_Lean_warningAsError;
                        v___x_9096_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_9087_, v___x_9095_);
                        v___y_9076_ = v_fileName_9085_;
                        v___y_9077_ = v___f_9092_;
                        v___y_9078_ = v_suppressElabErrors_9089_;
                        v___y_9079_ = v_fileMap_9086_;
                        v___y_9080_ = v_ref_9088_;
                        v___y_9081_ = v___y_9084_;
                        v___y_9082_ = v___x_9096_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_8982_);
                    v___x_9097_ = lean_box(0);
                    v___x_9098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9098_, 0, v___x_9097_);
                    return v___x_9098_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(
    mut v_ref_9101_: *mut LeanObject,
    mut v_msgData_9102_: *mut LeanObject,
    mut v_severity_9103_: *mut LeanObject,
    mut v_isSilent_9104_: *mut LeanObject,
    mut v___y_9105_: *mut LeanObject,
    mut v___y_9106_: *mut LeanObject,
    mut v___y_9107_: *mut LeanObject,
    mut v___y_9108_: *mut LeanObject,
    mut v___y_9109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_9110_: u8 = 0;
    let mut v_isSilent_boxed_9111_: u8 = 0;
    let mut v_res_9112_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_9110_ = (lean_unbox(v_severity_9103_) as u8);
    v_isSilent_boxed_9111_ = (lean_unbox(v_isSilent_9104_) as u8);
    v_res_9112_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_9101_, v_msgData_9102_, v_severity_boxed_9110_, v_isSilent_boxed_9111_, v___y_9105_, v___y_9106_, v___y_9107_, v___y_9108_);
    lean_dec(v___y_9108_);
    lean_dec_ref(v___y_9107_);
    lean_dec(v___y_9106_);
    lean_dec_ref(v___y_9105_);
    lean_dec(v_ref_9101_);
    return v_res_9112_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(
    mut v_msgData_9113_: *mut LeanObject,
    mut v_severity_9114_: u8,
    mut v_isSilent_9115_: u8,
    mut v___y_9116_: *mut LeanObject,
    mut v___y_9117_: *mut LeanObject,
    mut v___y_9118_: *mut LeanObject,
    mut v___y_9119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_9121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9122_: *mut LeanObject = core::ptr::null_mut();
    v_ref_9121_ = lean_ctor_get(v___y_9118_, 5);
    v___x_9122_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_9121_, v_msgData_9113_, v_severity_9114_, v_isSilent_9115_, v___y_9116_, v___y_9117_, v___y_9118_, v___y_9119_);
    return v___x_9122_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(
    mut v_msgData_9123_: *mut LeanObject,
    mut v_severity_9124_: *mut LeanObject,
    mut v_isSilent_9125_: *mut LeanObject,
    mut v___y_9126_: *mut LeanObject,
    mut v___y_9127_: *mut LeanObject,
    mut v___y_9128_: *mut LeanObject,
    mut v___y_9129_: *mut LeanObject,
    mut v___y_9130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_9131_: u8 = 0;
    let mut v_isSilent_boxed_9132_: u8 = 0;
    let mut v_res_9133_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_9131_ = (lean_unbox(v_severity_9124_) as u8);
    v_isSilent_boxed_9132_ = (lean_unbox(v_isSilent_9125_) as u8);
    v_res_9133_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_9123_, v_severity_boxed_9131_, v_isSilent_boxed_9132_, v___y_9126_, v___y_9127_, v___y_9128_, v___y_9129_);
    lean_dec(v___y_9129_);
    lean_dec_ref(v___y_9128_);
    lean_dec(v___y_9127_);
    lean_dec_ref(v___y_9126_);
    return v_res_9133_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(
    mut v_msgData_9134_: *mut LeanObject,
    mut v___y_9135_: *mut LeanObject,
    mut v___y_9136_: *mut LeanObject,
    mut v___y_9137_: *mut LeanObject,
    mut v___y_9138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9140_: u8 = 0;
    let mut v___x_9141_: u8 = 0;
    let mut v___x_9142_: *mut LeanObject = core::ptr::null_mut();
    v___x_9140_ = 2;
    v___x_9141_ = 0;
    v___x_9142_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_9134_, v___x_9140_, v___x_9141_, v___y_9135_, v___y_9136_, v___y_9137_, v___y_9138_);
    return v___x_9142_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(
    mut v_msgData_9143_: *mut LeanObject,
    mut v___y_9144_: *mut LeanObject,
    mut v___y_9145_: *mut LeanObject,
    mut v___y_9146_: *mut LeanObject,
    mut v___y_9147_: *mut LeanObject,
    mut v___y_9148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9149_: *mut LeanObject = core::ptr::null_mut();
    v_res_9149_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(
        v_msgData_9143_,
        v___y_9144_,
        v___y_9145_,
        v___y_9146_,
        v___y_9147_,
    );
    lean_dec(v___y_9147_);
    lean_dec_ref(v___y_9146_);
    lean_dec(v___y_9145_);
    lean_dec_ref(v___y_9144_);
    return v_res_9149_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_9151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9152_: *mut LeanObject = core::ptr::null_mut();
    v___x_9151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0;
    v___x_9152_ = l_Lean_stringToMessageData(v___x_9151_);
    return v___x_9152_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_9154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9155_: *mut LeanObject = core::ptr::null_mut();
    v___x_9154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2;
    v___x_9155_ = l_Lean_stringToMessageData(v___x_9154_);
    return v___x_9155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(
    mut v_as_9156_: *mut LeanObject,
    mut v_sz_9157_: usize,
    mut v_i_9158_: usize,
    mut v_b_9159_: *mut LeanObject,
    mut v___y_9160_: *mut LeanObject,
    mut v___y_9161_: *mut LeanObject,
    mut v___y_9162_: *mut LeanObject,
    mut v___y_9163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9167_: usize = 0;
    let mut v___x_9168_: usize = 0;
    let mut v___x_9170_: u8 = 0;
    let mut v___x_9171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9177_: u8 = 0;
    let mut v___x_9178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9183_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9170_ = lean_usize_dec_lt(v_i_9158_, v_sz_9157_);
                if v___x_9170_ == 0 {
                    v___x_9171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9171_, 0, v_b_9159_);
                    return v___x_9171_;
                } else {
                    v___x_9172_ = lean_st_ref_get(v___y_9163_);
                    v_env_9173_ = lean_ctor_get(v___x_9172_, 0);
                    lean_inc_ref(v_env_9173_);
                    lean_dec(v___x_9172_);
                    v___x_9174_ = lean_box(0);
                    v_a_9175_ = lean_array_uget_borrowed(v_as_9156_, v_i_9158_);
                    v___x_9176_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
                    lean_inc(v_a_9175_);
                    v___x_9177_ = l_Lean_TagAttribute_hasTag(v___x_9176_, v_env_9173_, v_a_9175_);
                    if v___x_9177_ == 0 {
                        v___x_9178_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
                        lean_inc(v_a_9175_);
                        v___x_9179_ = l_Lean_MessageData_ofName(v_a_9175_);
                        v___x_9180_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_9180_, 0, v___x_9178_);
                        lean_ctor_set(v___x_9180_, 1, v___x_9179_);
                        v___x_9181_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
                        v___x_9182_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_9182_, 0, v___x_9180_);
                        lean_ctor_set(v___x_9182_, 1, v___x_9181_);
                        v___x_9183_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_9182_, v___y_9160_, v___y_9161_, v___y_9162_, v___y_9163_);
                        if lean_obj_tag(v___x_9183_) == 0 {
                            lean_dec_ref_known(v___x_9183_, 1);
                            v_a_9166_ = v___x_9174_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_9183_;
                        }
                    } else {
                        v_a_9166_ = v___x_9174_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9167_ = 1usize;
                v___x_9168_ = lean_usize_add(v_i_9158_, v___x_9167_);
                v_i_9158_ = v___x_9168_;
                v_b_9159_ = v_a_9166_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(
    mut v_as_9184_: *mut LeanObject,
    mut v_sz_9185_: *mut LeanObject,
    mut v_i_9186_: *mut LeanObject,
    mut v_b_9187_: *mut LeanObject,
    mut v___y_9188_: *mut LeanObject,
    mut v___y_9189_: *mut LeanObject,
    mut v___y_9190_: *mut LeanObject,
    mut v___y_9191_: *mut LeanObject,
    mut v___y_9192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9193_: usize = 0;
    let mut v_i_boxed_9194_: usize = 0;
    let mut v_res_9195_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9193_ = lean_unbox_usize(v_sz_9185_);
    lean_dec(v_sz_9185_);
    v_i_boxed_9194_ = lean_unbox_usize(v_i_9186_);
    lean_dec(v_i_9186_);
    v_res_9195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_9184_, v_sz_boxed_9193_, v_i_boxed_9194_, v_b_9187_, v___y_9188_, v___y_9189_, v___y_9190_, v___y_9191_);
    lean_dec(v___y_9191_);
    lean_dec_ref(v___y_9190_);
    lean_dec(v___y_9189_);
    lean_dec_ref(v___y_9188_);
    lean_dec_ref(v_as_9184_);
    return v_res_9195_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(
    mut v_as_9196_: *mut LeanObject,
    mut v_sz_9197_: usize,
    mut v_i_9198_: usize,
    mut v_b_9199_: *mut LeanObject,
    mut v___y_9200_: *mut LeanObject,
    mut v___y_9201_: *mut LeanObject,
    mut v___y_9202_: *mut LeanObject,
    mut v___y_9203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9205_: u8 = 0;
    let mut v___x_9206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9211_: usize = 0;
    let mut v___x_9212_: usize = 0;
    let mut v___x_9213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9215_: usize = 0;
    let mut v___x_9216_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9205_ = lean_usize_dec_lt(v_i_9198_, v_sz_9197_);
                if v___x_9205_ == 0 {
                    v___x_9206_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9206_, 0, v_b_9199_);
                    return v___x_9206_;
                } else {
                    v_a_9207_ = lean_array_uget_borrowed(v_as_9196_, v_i_9198_);
                    v_fst_9208_ = lean_ctor_get(v_a_9207_, 0);
                    v_snd_9209_ = lean_ctor_get(v_a_9207_, 1);
                    v___x_9210_ = lean_box(0);
                    v_sz_9211_ = lean_array_size(v_snd_9209_);
                    v___x_9212_ = 0usize;
                    v___x_9213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_9209_, v_sz_9211_, v___x_9212_, v___x_9210_, v___y_9200_, v___y_9201_, v___y_9202_, v___y_9203_);
                    if lean_obj_tag(v___x_9213_) == 0 {
                        lean_dec_ref_known(v___x_9213_, 1);
                        lean_inc(v_snd_9209_);
                        lean_inc(v_fst_9208_);
                        v___x_9214_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(
                            v_fst_9208_,
                            v_snd_9209_,
                            v___y_9200_,
                            v___y_9201_,
                            v___y_9202_,
                            v___y_9203_,
                        );
                        if lean_obj_tag(v___x_9214_) == 0 {
                            lean_dec_ref_known(v___x_9214_, 1);
                            v___x_9215_ = 1usize;
                            v___x_9216_ = lean_usize_add(v_i_9198_, v___x_9215_);
                            v_i_9198_ = v___x_9216_;
                            v_b_9199_ = v___x_9210_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_9214_;
                        }
                    } else {
                        return v___x_9213_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(
    mut v_as_9218_: *mut LeanObject,
    mut v_sz_9219_: *mut LeanObject,
    mut v_i_9220_: *mut LeanObject,
    mut v_b_9221_: *mut LeanObject,
    mut v___y_9222_: *mut LeanObject,
    mut v___y_9223_: *mut LeanObject,
    mut v___y_9224_: *mut LeanObject,
    mut v___y_9225_: *mut LeanObject,
    mut v___y_9226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9227_: usize = 0;
    let mut v_i_boxed_9228_: usize = 0;
    let mut v_res_9229_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9227_ = lean_unbox_usize(v_sz_9219_);
    lean_dec(v_sz_9219_);
    v_i_boxed_9228_ = lean_unbox_usize(v_i_9220_);
    lean_dec(v_i_9220_);
    v_res_9229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_9218_, v_sz_boxed_9227_, v_i_boxed_9228_, v_b_9221_, v___y_9222_, v___y_9223_, v___y_9224_, v___y_9225_);
    lean_dec(v___y_9225_);
    lean_dec_ref(v___y_9224_);
    lean_dec(v___y_9223_);
    lean_dec_ref(v___y_9222_);
    lean_dec_ref(v_as_9218_);
    return v_res_9229_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(
    mut v_sz_9230_: usize,
    mut v_i_9231_: usize,
    mut v_bs_9232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9233_: u8 = 0;
    let mut v_v_9234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_9237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9241_: usize = 0;
    let mut v___x_9242_: usize = 0;
    let mut v___x_9243_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9233_ = lean_usize_dec_lt(v_i_9231_, v_sz_9230_);
                if v___x_9233_ == 0 {
                    return v_bs_9232_;
                } else {
                    v_v_9234_ = lean_array_uget_borrowed(v_bs_9232_, v_i_9231_);
                    v_fst_9235_ = lean_ctor_get(v_v_9234_, 0);
                    lean_inc(v_fst_9235_);
                    v___x_9236_ = lean_unsigned_to_nat(0);
                    v_bs_x27_9237_ = lean_array_uset(v_bs_9232_, v_i_9231_, v___x_9236_);
                    v___x_9238_ = l_Lean_mkCasesOnName(v_fst_9235_);
                    v___x_9239_ = l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1;
                    v___x_9240_ = l_Lean_Name_append(v___x_9238_, v___x_9239_);
                    v___x_9241_ = 1usize;
                    v___x_9242_ = lean_usize_add(v_i_9231_, v___x_9241_);
                    v___x_9243_ = lean_array_uset(v_bs_x27_9237_, v_i_9231_, v___x_9240_);
                    v_i_9231_ = v___x_9242_;
                    v_bs_9232_ = v___x_9243_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(
    mut v_sz_9245_: *mut LeanObject,
    mut v_i_9246_: *mut LeanObject,
    mut v_bs_9247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9248_: usize = 0;
    let mut v_i_boxed_9249_: usize = 0;
    let mut v_res_9250_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9248_ = lean_unbox_usize(v_sz_9245_);
    lean_dec(v_sz_9245_);
    v_i_boxed_9249_ = lean_unbox_usize(v_i_9246_);
    lean_dec(v_i_9246_);
    v_res_9250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_9248_, v_i_boxed_9249_, v_bs_9247_);
    return v_res_9250_;
}
pub unsafe fn l_Lean_Elab_ComputedFields_setComputedFields(
    mut v_computedFields_9253_: *mut LeanObject,
    mut v_a_9254_: *mut LeanObject,
    mut v_a_9255_: *mut LeanObject,
    mut v_a_9256_: *mut LeanObject,
    mut v_a_9257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9260_: usize = 0;
    let mut v___x_9261_: usize = 0;
    let mut v___x_9262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9264_: u8 = 0;
    let mut v___x_9265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9273_: u8 = 0;
    let mut v___x_9275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9259_ = lean_box(0);
                v_sz_9260_ = lean_array_size(v_computedFields_9253_);
                v___x_9261_ = 0usize;
                v___x_9262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_9253_, v_sz_9260_, v___x_9261_, v___x_9259_, v_a_9254_, v_a_9255_, v_a_9256_, v_a_9257_);
                if lean_obj_tag(v___x_9262_) == 0 {
                    lean_dec_ref_known(v___x_9262_, 1);
                    lean_inc_ref(v_computedFields_9253_);
                    v___x_9263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_9260_, v___x_9261_, v_computedFields_9253_);
                    v___x_9264_ = 1;
                    v___x_9265_ =
                        l_Lean_compileDecls(v___x_9263_, v___x_9264_, v_a_9256_, v_a_9257_);
                    if lean_obj_tag(v___x_9265_) == 0 {
                        lean_dec_ref_known(v___x_9265_, 1);
                        v___x_9266_ = l_Lean_Elab_ComputedFields_setComputedFields___closed__0;
                        v___x_9267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_9253_, v_sz_9260_, v___x_9261_, v___x_9266_, v_a_9254_, v_a_9255_, v_a_9256_, v_a_9257_);
                        lean_dec_ref(v_computedFields_9253_);
                        if lean_obj_tag(v___x_9267_) == 0 {
                            v_a_9268_ = lean_ctor_get(v___x_9267_, 0);
                            lean_inc(v_a_9268_);
                            lean_dec_ref_known(v___x_9267_, 1);
                            v___x_9269_ =
                                l_Lean_compileDecls(v_a_9268_, v___x_9264_, v_a_9256_, v_a_9257_);
                            return v___x_9269_;
                        } else {
                            v_a_9270_ = lean_ctor_get(v___x_9267_, 0);
                            v_isSharedCheck_9277_ = (!lean_is_exclusive(v___x_9267_)) as u8;
                            if v_isSharedCheck_9277_ == 0 {
                                v___x_9272_ = v___x_9267_;
                                v_isShared_9273_ = v_isSharedCheck_9277_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_9270_);
                                lean_dec(v___x_9267_);
                                v___x_9272_ = lean_box(0);
                                v_isShared_9273_ = v_isSharedCheck_9277_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_computedFields_9253_);
                        return v___x_9265_;
                    }
                } else {
                    lean_dec_ref(v_computedFields_9253_);
                    return v___x_9262_;
                }
            }
            1 => {
                if v_isShared_9273_ == 0 {
                    v___x_9275_ = v___x_9272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9276_, 0, v_a_9270_);
                    v___x_9275_ = v_reuseFailAlloc_9276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ComputedFields_setComputedFields___boxed(
    mut v_computedFields_9278_: *mut LeanObject,
    mut v_a_9279_: *mut LeanObject,
    mut v_a_9280_: *mut LeanObject,
    mut v_a_9281_: *mut LeanObject,
    mut v_a_9282_: *mut LeanObject,
    mut v_a_9283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9284_: *mut LeanObject = core::ptr::null_mut();
    v_res_9284_ = l_Lean_Elab_ComputedFields_setComputedFields(
        v_computedFields_9278_,
        v_a_9279_,
        v_a_9280_,
        v_a_9281_,
        v_a_9282_,
    );
    lean_dec(v_a_9282_);
    lean_dec_ref(v_a_9281_);
    lean_dec(v_a_9280_);
    lean_dec_ref(v_a_9279_);
    return v_res_9284_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(
    mut v_as_9285_: *mut LeanObject,
    mut v_as_x27_9286_: *mut LeanObject,
    mut v_b_9287_: *mut LeanObject,
    mut v_a_9288_: *mut LeanObject,
    mut v___y_9289_: *mut LeanObject,
    mut v___y_9290_: *mut LeanObject,
    mut v___y_9291_: *mut LeanObject,
    mut v___y_9292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9294_: *mut LeanObject = core::ptr::null_mut();
    v___x_9294_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(
            v_as_x27_9286_,
            v_b_9287_,
        );
    return v___x_9294_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(
    mut v_as_9295_: *mut LeanObject,
    mut v_as_x27_9296_: *mut LeanObject,
    mut v_b_9297_: *mut LeanObject,
    mut v_a_9298_: *mut LeanObject,
    mut v___y_9299_: *mut LeanObject,
    mut v___y_9300_: *mut LeanObject,
    mut v___y_9301_: *mut LeanObject,
    mut v___y_9302_: *mut LeanObject,
    mut v___y_9303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9304_: *mut LeanObject = core::ptr::null_mut();
    v_res_9304_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(
        v_as_9295_,
        v_as_x27_9296_,
        v_b_9297_,
        v_a_9298_,
        v___y_9299_,
        v___y_9300_,
        v___y_9301_,
        v___y_9302_,
    );
    lean_dec(v___y_9302_);
    lean_dec_ref(v___y_9301_);
    lean_dec(v___y_9300_);
    lean_dec_ref(v___y_9299_);
    lean_dec(v_as_x27_9296_);
    lean_dec(v_as_9295_);
    return v_res_9304_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(
    mut v_as_9305_: *mut LeanObject,
    mut v_sz_9306_: usize,
    mut v_i_9307_: usize,
    mut v_b_9308_: *mut LeanObject,
    mut v___y_9309_: *mut LeanObject,
    mut v___y_9310_: *mut LeanObject,
    mut v___y_9311_: *mut LeanObject,
    mut v___y_9312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9314_: *mut LeanObject = core::ptr::null_mut();
    v___x_9314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_9305_, v_sz_9306_, v_i_9307_, v_b_9308_, v___y_9312_);
    return v___x_9314_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(
    mut v_as_9315_: *mut LeanObject,
    mut v_sz_9316_: *mut LeanObject,
    mut v_i_9317_: *mut LeanObject,
    mut v_b_9318_: *mut LeanObject,
    mut v___y_9319_: *mut LeanObject,
    mut v___y_9320_: *mut LeanObject,
    mut v___y_9321_: *mut LeanObject,
    mut v___y_9322_: *mut LeanObject,
    mut v___y_9323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_9324_: usize = 0;
    let mut v_i_boxed_9325_: usize = 0;
    let mut v_res_9326_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_9324_ = lean_unbox_usize(v_sz_9316_);
    lean_dec(v_sz_9316_);
    v_i_boxed_9325_ = lean_unbox_usize(v_i_9317_);
    lean_dec(v_i_9317_);
    v_res_9326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_9315_, v_sz_boxed_9324_, v_i_boxed_9325_, v_b_9318_, v___y_9319_, v___y_9320_, v___y_9321_, v___y_9322_);
    lean_dec(v___y_9322_);
    lean_dec_ref(v___y_9321_);
    lean_dec(v___y_9320_);
    lean_dec_ref(v___y_9319_);
    lean_dec_ref(v_as_9315_);
    return v_res_9326_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ComputedFields(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_ComputedFields_computedFieldAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_ComputedFields_computedFieldAttr);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ComputedFields_0__Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ComputedFields(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ComputedFields(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_ExternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ComputedFields(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ComputedFields(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ComputedFields(builtin);
}
