// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: Lean.Compiler.InitAttr Lean.Compiler.LCNF.ToLCNF Lean.Compiler.Options Lean.Meta.Transform Lean.Meta.Match.MatcherInfo Init.While Lean.Compiler.ExportAttr
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_instantiate_rev, lean_infer_type,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_ptr_addr,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Compiler::BorrowedAnnotation::l_Lean_isMarkedBorrowed;
use crate::r#gen::Lean::Compiler::ExportAttr::{
    initialize_Lean_Compiler_ExportAttr, l_Lean_isExport,
    runtime_initialize_Lean_Compiler_ExportAttr,
};
use crate::r#gen::Lean::Compiler::ExternAttr::l_Lean_getExternAttrData_x3f;
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_hasInitAttr,
    runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Compiler::InlineAttrs::{
    l_Lean_Compiler_getInlineAttribute_x3f, l_Lean_Compiler_hasMacroInlineAttribute,
};
use crate::r#gen::Lean::Compiler::LCNF::Bind::l_Lean_Compiler_LCNF_Decl_etaExpand;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg,
    l_Lean_Compiler_LCNF_eraseFunDecl___redArg, l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_mkParam,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::ToLCNF::{
    initialize_Lean_Compiler_LCNF_ToLCNF, l_Lean_Compiler_LCNF_ToLCNF_toLCNF,
    runtime_initialize_Lean_Compiler_LCNF_ToLCNF,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_toLCNFType;
use crate::r#gen::Lean::Compiler::Old::{
    l_Lean_Compiler_isUnsafeRecName_x3f, l_Lean_Compiler_mkUnsafeRecName,
};
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_ignoreBorrowAnnotation,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instantiateValueLevelParams, l_Lean_Core_mkFreshUserName,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_isUnsafe, l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type,
    l_Lean_ConstantInfo_value_x3f,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_interruptExceptionId, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta,
    l_Lean_Expr_const___override, l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConst, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instInhabitedExpr, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_etaExpand,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    initialize_Lean_Meta_Match_MatcherInfo, l_Lean_Meta_Match_Extension_getMatcherInfo_x3f,
    l_Lean_Meta_Match_MatcherInfo_altNumParams, l_Lean_Meta_Match_MatcherInfo_arity,
    l_Lean_Meta_Match_MatcherInfo_getFirstAltPos, l_Lean_Meta_isMatcherLikeCore,
    runtime_initialize_Lean_Meta_Match_MatcherInfo,
};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_macroInline___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_macroInline___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_macroInline___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_macroInline___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_macroInline___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_macroInline___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_macroInline___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_macroInline___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 107, 0]};
static mut l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0_value) as *mut leanh::LeanObject,15426200077562993723 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__2_value: leanh::LeanClosureObject<2> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 97, 108, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0_value) as *mut leanh::LeanObject,3290733903363786515 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_inlineMatchers___closed__0_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut leanh::LeanObject,
            72621647814721793 as *mut leanh::LeanObject,
            65793 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inlineMatchers___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__1: u64 = 0;
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_inlineMatchers___closed__6_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inlineMatchers___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_inlineMatchers___closed__12_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inlineMatchers___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_inlineMatchers___closed__13_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_inlineMatchers___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inlineMatchers___closed__13_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_toDecl___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [32, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toDecl___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toDecl___closed__2_value: leanh::LeanStringObject<321> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 321,
        m_capacity: 321,
        m_length: 320,
        m_data: [
            32, 105, 115, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 96, 101, 120, 112, 111,
            114, 116, 96, 32, 98, 117, 116, 32, 115, 111, 109, 101, 32, 111, 102, 32, 105, 116,
            115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 104, 97, 118, 101, 32, 98,
            111, 114, 114, 111, 119, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 46,
            10, 32, 67, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 96,
            115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 99, 111, 109, 112, 105, 108, 101,
            114, 46, 105, 103, 110, 111, 114, 101, 66, 111, 114, 114, 111, 119, 65, 110, 110, 111,
            116, 97, 116, 105, 111, 110, 32, 116, 114, 117, 101, 32, 105, 110, 96, 32, 116, 111,
            32, 115, 117, 112, 112, 114, 101, 115, 115, 32, 116, 104, 101, 32, 98, 111, 114, 114,
            111, 119, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32, 105, 110, 32,
            105, 116, 115, 32, 116, 121, 112, 101, 46, 10, 32, 73, 102, 32, 116, 104, 101, 32, 100,
            101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 105, 115, 32, 112, 97, 114, 116, 32,
            111, 102, 32, 97, 110, 32, 96, 101, 120, 112, 111, 114, 116, 96, 47, 96, 101, 120, 116,
            101, 114, 110, 96, 32, 112, 97, 105, 114, 32, 109, 97, 107, 101, 32, 115, 117, 114,
            101, 32, 116, 111, 32, 97, 108, 115, 111, 32, 115, 117, 112, 112, 114, 101, 115, 115,
            32, 116, 104, 101, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32, 97,
            116, 32, 116, 104, 101, 32, 96, 101, 120, 116, 101, 114, 110, 96, 32, 100, 101, 99,
            108, 97, 114, 97, 116, 105, 111, 110, 46, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toDecl___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toDecl___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_toDecl___closed__5_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toDecl___closed__7_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 32, 118,
            97, 108, 117, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toDecl___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toDecl___closed__9_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [96, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toDecl___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toDecl___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toDecl___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_macroInline___lam__0(
    mut v_e_4284_: *mut leanh::LeanObject,
    mut v___y_4285_: *mut leanh::LeanObject,
    mut v___y_4286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4288_, 0, v_e_4284_);
    v___x_4289_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4289_, 0, v___x_4288_);
    return v___x_4289_;
}
pub unsafe fn l_Lean_Compiler_LCNF_macroInline___lam__0___boxed(
    mut v_e_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
    mut v___y_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4294_ = l_Lean_Compiler_LCNF_macroInline___lam__0(v_e_4290_, v___y_4291_, v___y_4292_);
    leanh::lean_dec(v___y_4292_);
    leanh::lean_dec_ref(v___y_4291_);
    return v_res_4294_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4295_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__0);
    v___x_4297_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4297_, 0, v___x_4296_);
    return v___x_4297_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4298_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1);
    v___x_4299_ = leanh::lean_unsigned_to_nat(0);
    v___x_4300_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4300_, 0, v___x_4299_);
    leanh::lean_ctor_set(v___x_4300_, 1, v___x_4299_);
    leanh::lean_ctor_set(v___x_4300_, 2, v___x_4299_);
    leanh::lean_ctor_set(v___x_4300_, 3, v___x_4299_);
    leanh::lean_ctor_set(v___x_4300_, 4, v___x_4298_);
    leanh::lean_ctor_set(v___x_4300_, 5, v___x_4298_);
    leanh::lean_ctor_set(v___x_4300_, 6, v___x_4298_);
    leanh::lean_ctor_set(v___x_4300_, 7, v___x_4298_);
    leanh::lean_ctor_set(v___x_4300_, 8, v___x_4298_);
    leanh::lean_ctor_set(v___x_4300_, 9, v___x_4298_);
    return v___x_4300_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4301_ = leanh::lean_unsigned_to_nat(32);
    v___x_4302_ = lean_mk_empty_array_with_capacity(v___x_4301_);
    v___x_4303_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4303_, 0, v___x_4302_);
    return v___x_4303_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4304_: usize = 0;
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4304_ = 5usize;
    v___x_4305_ = leanh::lean_unsigned_to_nat(0);
    v___x_4306_ = leanh::lean_unsigned_to_nat(32);
    v___x_4307_ = lean_mk_empty_array_with_capacity(v___x_4306_);
    v___x_4308_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__3);
    v___x_4309_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4309_, 0, v___x_4308_);
    leanh::lean_ctor_set(v___x_4309_, 1, v___x_4307_);
    leanh::lean_ctor_set(v___x_4309_, 2, v___x_4305_);
    leanh::lean_ctor_set(v___x_4309_, 3, v___x_4305_);
    leanh::lean_ctor_set_usize(v___x_4309_, 4, v___x_4304_);
    return v___x_4309_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4310_ = leanh::lean_box(1);
    v___x_4311_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4);
    v___x_4312_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__1);
    v___x_4313_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4313_, 0, v___x_4312_);
    leanh::lean_ctor_set(v___x_4313_, 1, v___x_4311_);
    leanh::lean_ctor_set(v___x_4313_, 2, v___x_4310_);
    return v___x_4313_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21(
    mut v_msgData_4314_: *mut leanh::LeanObject,
    mut v___y_4315_: *mut leanh::LeanObject,
    mut v___y_4316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = lean_st_ref_get(v___y_4316_);
    v_env_4319_ = leanh::lean_ctor_get(v___x_4318_, 0);
    leanh::lean_inc_ref(v_env_4319_);
    leanh::lean_dec(v___x_4318_);
    v_options_4320_ = leanh::lean_ctor_get(v___y_4315_, 2);
    v___x_4321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2);
    v___x_4322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5);
    leanh::lean_inc_ref(v_options_4320_);
    v___x_4323_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4323_, 0, v_env_4319_);
    leanh::lean_ctor_set(v___x_4323_, 1, v___x_4321_);
    leanh::lean_ctor_set(v___x_4323_, 2, v___x_4322_);
    leanh::lean_ctor_set(v___x_4323_, 3, v_options_4320_);
    v___x_4324_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4324_, 0, v___x_4323_);
    leanh::lean_ctor_set(v___x_4324_, 1, v_msgData_4314_);
    v___x_4325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4325_, 0, v___x_4324_);
    return v___x_4325_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___boxed(
    mut v_msgData_4326_: *mut leanh::LeanObject,
    mut v___y_4327_: *mut leanh::LeanObject,
    mut v___y_4328_: *mut leanh::LeanObject,
    mut v___y_4329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4330_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21(v_msgData_4326_, v___y_4327_, v___y_4328_);
    leanh::lean_dec(v___y_4328_);
    leanh::lean_dec_ref(v___y_4327_);
    return v_res_4330_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16___redArg(
    mut v_msg_4331_: *mut leanh::LeanObject,
    mut v___y_4332_: *mut leanh::LeanObject,
    mut v___y_4333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4340_: u8 = 0;
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4335_ = leanh::lean_ctor_get(v___y_4332_, 5);
                v___x_4336_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21(v_msg_4331_, v___y_4332_, v___y_4333_);
                v_a_4337_ = leanh::lean_ctor_get(v___x_4336_, 0);
                v_isSharedCheck_4345_ = (!leanh::lean_is_exclusive(v___x_4336_)) as u8;
                if v_isSharedCheck_4345_ == 0 {
                    v___x_4339_ = v___x_4336_;
                    v_isShared_4340_ = v_isSharedCheck_4345_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4337_);
                    leanh::lean_dec(v___x_4336_);
                    v___x_4339_ = leanh::lean_box(0);
                    v_isShared_4340_ = v_isSharedCheck_4345_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4335_);
                v___x_4341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4341_, 0, v_ref_4335_);
                leanh::lean_ctor_set(v___x_4341_, 1, v_a_4337_);
                if v_isShared_4340_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4339_, 1);
                    leanh::lean_ctor_set(v___x_4339_, 0, v___x_4341_);
                    v___x_4343_ = v___x_4339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
                    v___x_4343_ = v_reuseFailAlloc_4344_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16___redArg___boxed(
    mut v_msg_4346_: *mut leanh::LeanObject,
    mut v___y_4347_: *mut leanh::LeanObject,
    mut v___y_4348_: *mut leanh::LeanObject,
    mut v___y_4349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4350_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16___redArg(v_msg_4346_, v___y_4347_, v___y_4348_);
    leanh::lean_dec(v___y_4348_);
    leanh::lean_dec_ref(v___y_4347_);
    return v_res_4350_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_ref_4351_: *mut leanh::LeanObject,
    mut v_msg_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
    mut v___y_4354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4368_: u8 = 0;
    let mut v_cancelTk_x3f_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4370_: u8 = 0;
    let mut v_inheritedTraceOptions_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4356_ = leanh::lean_ctor_get(v___y_4353_, 0);
    v_fileMap_4357_ = leanh::lean_ctor_get(v___y_4353_, 1);
    v_options_4358_ = leanh::lean_ctor_get(v___y_4353_, 2);
    v_currRecDepth_4359_ = leanh::lean_ctor_get(v___y_4353_, 3);
    v_maxRecDepth_4360_ = leanh::lean_ctor_get(v___y_4353_, 4);
    v_ref_4361_ = leanh::lean_ctor_get(v___y_4353_, 5);
    v_currNamespace_4362_ = leanh::lean_ctor_get(v___y_4353_, 6);
    v_openDecls_4363_ = leanh::lean_ctor_get(v___y_4353_, 7);
    v_initHeartbeats_4364_ = leanh::lean_ctor_get(v___y_4353_, 8);
    v_maxHeartbeats_4365_ = leanh::lean_ctor_get(v___y_4353_, 9);
    v_quotContext_4366_ = leanh::lean_ctor_get(v___y_4353_, 10);
    v_currMacroScope_4367_ = leanh::lean_ctor_get(v___y_4353_, 11);
    v_diag_4368_ = leanh::lean_ctor_get_uint8(
        v___y_4353_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4369_ = leanh::lean_ctor_get(v___y_4353_, 12);
    v_suppressElabErrors_4370_ = leanh::lean_ctor_get_uint8(
        v___y_4353_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4371_ = leanh::lean_ctor_get(v___y_4353_, 13);
    v_ref_4372_ = l_Lean_replaceRef(v_ref_4351_, v_ref_4361_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_4371_);
    leanh::lean_inc(v_cancelTk_x3f_4369_);
    leanh::lean_inc(v_currMacroScope_4367_);
    leanh::lean_inc(v_quotContext_4366_);
    leanh::lean_inc(v_maxHeartbeats_4365_);
    leanh::lean_inc(v_initHeartbeats_4364_);
    leanh::lean_inc(v_openDecls_4363_);
    leanh::lean_inc(v_currNamespace_4362_);
    leanh::lean_inc(v_maxRecDepth_4360_);
    leanh::lean_inc(v_currRecDepth_4359_);
    leanh::lean_inc_ref(v_options_4358_);
    leanh::lean_inc_ref(v_fileMap_4357_);
    leanh::lean_inc_ref(v_fileName_4356_);
    v___x_4373_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_4373_, 0, v_fileName_4356_);
    leanh::lean_ctor_set(v___x_4373_, 1, v_fileMap_4357_);
    leanh::lean_ctor_set(v___x_4373_, 2, v_options_4358_);
    leanh::lean_ctor_set(v___x_4373_, 3, v_currRecDepth_4359_);
    leanh::lean_ctor_set(v___x_4373_, 4, v_maxRecDepth_4360_);
    leanh::lean_ctor_set(v___x_4373_, 5, v_ref_4372_);
    leanh::lean_ctor_set(v___x_4373_, 6, v_currNamespace_4362_);
    leanh::lean_ctor_set(v___x_4373_, 7, v_openDecls_4363_);
    leanh::lean_ctor_set(v___x_4373_, 8, v_initHeartbeats_4364_);
    leanh::lean_ctor_set(v___x_4373_, 9, v_maxHeartbeats_4365_);
    leanh::lean_ctor_set(v___x_4373_, 10, v_quotContext_4366_);
    leanh::lean_ctor_set(v___x_4373_, 11, v_currMacroScope_4367_);
    leanh::lean_ctor_set(v___x_4373_, 12, v_cancelTk_x3f_4369_);
    leanh::lean_ctor_set(v___x_4373_, 13, v_inheritedTraceOptions_4371_);
    leanh::lean_ctor_set_uint8(
        v___x_4373_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_4368_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4373_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4370_,
    );
    v___x_4374_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16___redArg(v_msg_4352_, v___x_4373_, v___y_4354_);
    leanh::lean_dec_ref_known(v___x_4373_, 14);
    return v___x_4374_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_ref_4375_: *mut leanh::LeanObject,
    mut v_msg_4376_: *mut leanh::LeanObject,
    mut v___y_4377_: *mut leanh::LeanObject,
    mut v___y_4378_: *mut leanh::LeanObject,
    mut v___y_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4380_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_4375_, v_msg_4376_, v___y_4377_, v___y_4378_);
    leanh::lean_dec(v___y_4378_);
    leanh::lean_dec_ref(v___y_4377_);
    leanh::lean_dec(v_ref_4375_);
    return v_res_4380_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__0;
    v___x_4383_ = l_Lean_stringToMessageData(v___x_4382_);
    return v___x_4383_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4385_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__2;
    v___x_4386_ = l_Lean_stringToMessageData(v___x_4385_);
    return v___x_4386_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4388_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__4;
    v___x_4389_ = l_Lean_stringToMessageData(v___x_4388_);
    return v___x_4389_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4391_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__6;
    v___x_4392_ = l_Lean_stringToMessageData(v___x_4391_);
    return v___x_4392_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__8;
    v___x_4395_ = l_Lean_stringToMessageData(v___x_4394_);
    return v___x_4395_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__10;
    v___x_4398_ = l_Lean_stringToMessageData(v___x_4397_);
    return v___x_4398_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4400_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__12;
    v___x_4401_ = l_Lean_stringToMessageData(v___x_4400_);
    return v___x_4401_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg(
    mut v_msg_4402_: *mut leanh::LeanObject,
    mut v_declHint_4403_: *mut leanh::LeanObject,
    mut v___y_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    let mut v_isExporting_4409_: u8 = 0;
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4463_: u8 = 0;
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4406_ = lean_st_ref_get(v___y_4404_);
                v_env_4407_ = leanh::lean_ctor_get(v___x_4406_, 0);
                leanh::lean_inc_ref(v_env_4407_);
                leanh::lean_dec(v___x_4406_);
                v___x_4408_ = l_Lean_Name_isAnonymous(v_declHint_4403_);
                if v___x_4408_ == 0 {
                    v_isExporting_4409_ = leanh::lean_ctor_get_uint8(
                        v_env_4407_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4409_ == 0 {
                        leanh::lean_dec_ref(v_env_4407_);
                        leanh::lean_dec(v_declHint_4403_);
                        v___x_4410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4410_, 0, v_msg_4402_);
                        return v___x_4410_;
                    } else {
                        leanh::lean_inc_ref(v_env_4407_);
                        v___x_4411_ = l_Lean_Environment_setExporting(v_env_4407_, v___x_4408_);
                        leanh::lean_inc(v_declHint_4403_);
                        leanh::lean_inc_ref(v___x_4411_);
                        v___x_4412_ = l_Lean_Environment_contains(
                            v___x_4411_,
                            v_declHint_4403_,
                            v_isExporting_4409_,
                        );
                        if v___x_4412_ == 0 {
                            leanh::lean_dec_ref(v___x_4411_);
                            leanh::lean_dec_ref(v_env_4407_);
                            leanh::lean_dec(v_declHint_4403_);
                            v___x_4413_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4413_, 0, v_msg_4402_);
                            return v___x_4413_;
                        } else {
                            v___x_4414_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2);
                            v___x_4415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5);
                            v___x_4416_ = l_Lean_Options_empty;
                            v___x_4417_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_4417_, 0, v___x_4411_);
                            leanh::lean_ctor_set(v___x_4417_, 1, v___x_4414_);
                            leanh::lean_ctor_set(v___x_4417_, 2, v___x_4415_);
                            leanh::lean_ctor_set(v___x_4417_, 3, v___x_4416_);
                            leanh::lean_inc(v_declHint_4403_);
                            v___x_4418_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4403_, v___x_4408_);
                            v_c_4419_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_4419_, 0, v___x_4417_);
                            leanh::lean_ctor_set(v_c_4419_, 1, v___x_4418_);
                            v___x_4420_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4407_,
                                v_declHint_4403_,
                            );
                            if leanh::lean_obj_tag(v___x_4420_) == 0 {
                                leanh::lean_dec_ref(v_env_4407_);
                                leanh::lean_dec(v_declHint_4403_);
                                v___x_4421_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1);
                                v___x_4422_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4422_, 0, v___x_4421_);
                                leanh::lean_ctor_set(v___x_4422_, 1, v_c_4419_);
                                v___x_4423_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3);
                                v___x_4424_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4424_, 0, v___x_4422_);
                                leanh::lean_ctor_set(v___x_4424_, 1, v___x_4423_);
                                v___x_4425_ = l_Lean_MessageData_note(v___x_4424_);
                                v___x_4426_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4426_, 0, v_msg_4402_);
                                leanh::lean_ctor_set(v___x_4426_, 1, v___x_4425_);
                                v___x_4427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4427_, 0, v___x_4426_);
                                return v___x_4427_;
                            } else {
                                v_val_4428_ = leanh::lean_ctor_get(v___x_4420_, 0);
                                v_isSharedCheck_4463_ =
                                    (!leanh::lean_is_exclusive(v___x_4420_)) as u8;
                                if v_isSharedCheck_4463_ == 0 {
                                    v___x_4430_ = v___x_4420_;
                                    v_isShared_4431_ = v_isSharedCheck_4463_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4428_);
                                    leanh::lean_dec(v___x_4420_);
                                    v___x_4430_ = leanh::lean_box(0);
                                    v_isShared_4431_ = v_isSharedCheck_4463_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4407_);
                    leanh::lean_dec(v_declHint_4403_);
                    v___x_4464_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4464_, 0, v_msg_4402_);
                    return v___x_4464_;
                }
            }
            1 => {
                v___x_4432_ = leanh::lean_box(0);
                v___x_4433_ = l_Lean_Environment_header(v_env_4407_);
                leanh::lean_dec_ref(v_env_4407_);
                v___x_4434_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4433_);
                v_mod_4435_ = lean_array_get(v___x_4432_, v___x_4434_, v_val_4428_);
                leanh::lean_dec(v_val_4428_);
                leanh::lean_dec_ref(v___x_4434_);
                v___x_4436_ = l_Lean_isPrivateName(v_declHint_4403_);
                leanh::lean_dec(v_declHint_4403_);
                if v___x_4436_ == 0 {
                    v___x_4437_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5);
                    v___x_4438_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4438_, 0, v___x_4437_);
                    leanh::lean_ctor_set(v___x_4438_, 1, v_c_4419_);
                    v___x_4439_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7);
                    v___x_4440_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4440_, 0, v___x_4438_);
                    leanh::lean_ctor_set(v___x_4440_, 1, v___x_4439_);
                    v___x_4441_ = l_Lean_MessageData_ofName(v_mod_4435_);
                    v___x_4442_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4442_, 0, v___x_4440_);
                    leanh::lean_ctor_set(v___x_4442_, 1, v___x_4441_);
                    v___x_4443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9);
                    v___x_4444_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4444_, 0, v___x_4442_);
                    leanh::lean_ctor_set(v___x_4444_, 1, v___x_4443_);
                    v___x_4445_ = l_Lean_MessageData_note(v___x_4444_);
                    v___x_4446_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4446_, 0, v_msg_4402_);
                    leanh::lean_ctor_set(v___x_4446_, 1, v___x_4445_);
                    if v_isShared_4431_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4430_, 0);
                        leanh::lean_ctor_set(v___x_4430_, 0, v___x_4446_);
                        v___x_4448_ = v___x_4430_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4449_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
                        v___x_4448_ = v_reuseFailAlloc_4449_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4450_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1);
                    v___x_4451_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4451_, 0, v___x_4450_);
                    leanh::lean_ctor_set(v___x_4451_, 1, v_c_4419_);
                    v___x_4452_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11);
                    v___x_4453_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4453_, 0, v___x_4451_);
                    leanh::lean_ctor_set(v___x_4453_, 1, v___x_4452_);
                    v___x_4454_ = l_Lean_MessageData_ofName(v_mod_4435_);
                    v___x_4455_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4455_, 0, v___x_4453_);
                    leanh::lean_ctor_set(v___x_4455_, 1, v___x_4454_);
                    v___x_4456_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13);
                    v___x_4457_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4457_, 0, v___x_4455_);
                    leanh::lean_ctor_set(v___x_4457_, 1, v___x_4456_);
                    v___x_4458_ = l_Lean_MessageData_note(v___x_4457_);
                    v___x_4459_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4459_, 0, v_msg_4402_);
                    leanh::lean_ctor_set(v___x_4459_, 1, v___x_4458_);
                    if v_isShared_4431_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4430_, 0);
                        leanh::lean_ctor_set(v___x_4430_, 0, v___x_4459_);
                        v___x_4461_ = v___x_4430_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
                        v___x_4461_ = v_reuseFailAlloc_4462_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4448_;
            }
            3 => {
                return v___x_4461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___boxed(
    mut v_msg_4465_: *mut leanh::LeanObject,
    mut v_declHint_4466_: *mut leanh::LeanObject,
    mut v___y_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg(v_msg_4465_, v_declHint_4466_, v___y_4467_);
    leanh::lean_dec(v___y_4467_);
    return v_res_4469_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_msg_4470_: *mut leanh::LeanObject,
    mut v_declHint_4471_: *mut leanh::LeanObject,
    mut v___y_4472_: *mut leanh::LeanObject,
    mut v___y_4473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4475_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg(v_msg_4470_, v_declHint_4471_, v___y_4473_);
                v_a_4476_ = leanh::lean_ctor_get(v___x_4475_, 0);
                v_isSharedCheck_4485_ = (!leanh::lean_is_exclusive(v___x_4475_)) as u8;
                if v_isSharedCheck_4485_ == 0 {
                    v___x_4478_ = v___x_4475_;
                    v_isShared_4479_ = v_isSharedCheck_4485_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4476_);
                    leanh::lean_dec(v___x_4475_);
                    v___x_4478_ = leanh::lean_box(0);
                    v_isShared_4479_ = v_isSharedCheck_4485_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4480_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4481_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4481_, 0, v___x_4480_);
                leanh::lean_ctor_set(v___x_4481_, 1, v_a_4476_);
                if v_isShared_4479_ == 0 {
                    leanh::lean_ctor_set(v___x_4478_, 0, v___x_4481_);
                    v___x_4483_ = v___x_4478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
                    v___x_4483_ = v_reuseFailAlloc_4484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_msg_4486_: *mut leanh::LeanObject,
    mut v_declHint_4487_: *mut leanh::LeanObject,
    mut v___y_4488_: *mut leanh::LeanObject,
    mut v___y_4489_: *mut leanh::LeanObject,
    mut v___y_4490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4491_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_4486_, v_declHint_4487_, v___y_4488_, v___y_4489_);
    leanh::lean_dec(v___y_4489_);
    leanh::lean_dec_ref(v___y_4488_);
    return v_res_4491_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_4492_: *mut leanh::LeanObject,
    mut v_msg_4493_: *mut leanh::LeanObject,
    mut v_declHint_4494_: *mut leanh::LeanObject,
    mut v___y_4495_: *mut leanh::LeanObject,
    mut v___y_4496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_4493_, v_declHint_4494_, v___y_4495_, v___y_4496_);
    v_a_4499_ = leanh::lean_ctor_get(v___x_4498_, 0);
    leanh::lean_inc(v_a_4499_);
    leanh::lean_dec_ref(v___x_4498_);
    v___x_4500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_4492_, v_a_4499_, v___y_4495_, v___y_4496_);
    return v___x_4500_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_4501_: *mut leanh::LeanObject,
    mut v_msg_4502_: *mut leanh::LeanObject,
    mut v_declHint_4503_: *mut leanh::LeanObject,
    mut v___y_4504_: *mut leanh::LeanObject,
    mut v___y_4505_: *mut leanh::LeanObject,
    mut v___y_4506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4507_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4501_, v_msg_4502_, v_declHint_4503_, v___y_4504_, v___y_4505_);
    leanh::lean_dec(v___y_4505_);
    leanh::lean_dec_ref(v___y_4504_);
    leanh::lean_dec(v_ref_4501_);
    return v_res_4507_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4509_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4510_ = l_Lean_stringToMessageData(v___x_4509_);
    return v___x_4510_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_4513_ = l_Lean_stringToMessageData(v___x_4512_);
    return v___x_4513_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4514_: *mut leanh::LeanObject,
    mut v_constName_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: u8 = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4520_ = 0;
    leanh::lean_inc(v_constName_4515_);
    v___x_4521_ = l_Lean_MessageData_ofConstName(v_constName_4515_, v___x_4520_);
    v___x_4522_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4522_, 0, v___x_4519_);
    leanh::lean_ctor_set(v___x_4522_, 1, v___x_4521_);
    v___x_4523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_4524_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4524_, 0, v___x_4522_);
    leanh::lean_ctor_set(v___x_4524_, 1, v___x_4523_);
    v___x_4525_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4514_, v___x_4524_, v_constName_4515_, v___y_4516_, v___y_4517_);
    return v___x_4525_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4526_: *mut leanh::LeanObject,
    mut v_constName_4527_: *mut leanh::LeanObject,
    mut v___y_4528_: *mut leanh::LeanObject,
    mut v___y_4529_: *mut leanh::LeanObject,
    mut v___y_4530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg(v_ref_4526_, v_constName_4527_, v___y_4528_, v___y_4529_);
    leanh::lean_dec(v___y_4529_);
    leanh::lean_dec_ref(v___y_4528_);
    leanh::lean_dec(v_ref_4526_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0___redArg(
    mut v_constName_4532_: *mut leanh::LeanObject,
    mut v___y_4533_: *mut leanh::LeanObject,
    mut v___y_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4536_ = leanh::lean_ctor_get(v___y_4533_, 5);
    v___x_4537_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg(v_ref_4536_, v_constName_4532_, v___y_4533_, v___y_4534_);
    return v___x_4537_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0___redArg___boxed(
    mut v_constName_4538_: *mut leanh::LeanObject,
    mut v___y_4539_: *mut leanh::LeanObject,
    mut v___y_4540_: *mut leanh::LeanObject,
    mut v___y_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0___redArg(v_constName_4538_, v___y_4539_, v___y_4540_);
    leanh::lean_dec(v___y_4540_);
    leanh::lean_dec_ref(v___y_4539_);
    return v_res_4542_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0(
    mut v_constName_4543_: *mut leanh::LeanObject,
    mut v___y_4544_: *mut leanh::LeanObject,
    mut v___y_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: u8 = 0;
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4547_ = lean_st_ref_get(v___y_4545_);
                v_env_4548_ = leanh::lean_ctor_get(v___x_4547_, 0);
                leanh::lean_inc_ref(v_env_4548_);
                leanh::lean_dec(v___x_4547_);
                v___x_4549_ = 0;
                leanh::lean_inc(v_constName_4543_);
                v___x_4550_ =
                    l_Lean_Environment_find_x3f(v_env_4548_, v_constName_4543_, v___x_4549_);
                if leanh::lean_obj_tag(v___x_4550_) == 0 {
                    v___x_4551_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0___redArg(v_constName_4543_, v___y_4544_, v___y_4545_);
                    return v___x_4551_;
                } else {
                    leanh::lean_dec(v_constName_4543_);
                    v_val_4552_ = leanh::lean_ctor_get(v___x_4550_, 0);
                    v_isSharedCheck_4559_ = (!leanh::lean_is_exclusive(v___x_4550_)) as u8;
                    if v_isSharedCheck_4559_ == 0 {
                        v___x_4554_ = v___x_4550_;
                        v_isShared_4555_ = v_isSharedCheck_4559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4552_);
                        leanh::lean_dec(v___x_4550_);
                        v___x_4554_ = leanh::lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4555_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4554_, 0);
                    v___x_4557_ = v___x_4554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_val_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0___boxed(
    mut v_constName_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4564_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0(
        v_constName_4560_,
        v___y_4561_,
        v___y_4562_,
    );
    leanh::lean_dec(v___y_4562_);
    leanh::lean_dec_ref(v___y_4561_);
    return v_res_4564_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4567_ = leanh::lean_box(0);
    v_dummy_4568_ = l_Lean_Expr_sort___override(v___x_4567_);
    return v_dummy_4568_;
}
pub unsafe fn l_Lean_Compiler_LCNF_macroInline___lam__1(
    mut v_e_4569_: *mut leanh::LeanObject,
    mut v___y_4570_: *mut leanh::LeanObject,
    mut v___y_4571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v_dummy_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v_a_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4604_: u8 = 0;
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v_a_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4612_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4616_: u8 = 0;
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4573_ = l_Lean_Expr_getAppFn(v_e_4569_);
                if leanh::lean_obj_tag(v___x_4573_) == 4 {
                    v_declName_4574_ = leanh::lean_ctor_get(v___x_4573_, 0);
                    leanh::lean_inc_n(v_declName_4574_, 2);
                    v_us_4575_ = leanh::lean_ctor_get(v___x_4573_, 1);
                    leanh::lean_inc(v_us_4575_);
                    leanh::lean_dec_ref_known(v___x_4573_, 2);
                    v___x_4576_ = lean_st_ref_get(v___y_4571_);
                    v_env_4577_ = leanh::lean_ctor_get(v___x_4576_, 0);
                    leanh::lean_inc_ref(v_env_4577_);
                    leanh::lean_dec(v___x_4576_);
                    v___x_4578_ =
                        l_Lean_Compiler_hasMacroInlineAttribute(v_env_4577_, v_declName_4574_);
                    if v___x_4578_ == 0 {
                        leanh::lean_dec(v_us_4575_);
                        leanh::lean_dec(v_declName_4574_);
                        leanh::lean_dec_ref(v_e_4569_);
                        v___x_4579_ = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
                        v___x_4580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4580_, 0, v___x_4579_);
                        return v___x_4580_;
                    } else {
                        v___x_4581_ =
                            l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0(
                                v_declName_4574_,
                                v___y_4570_,
                                v___y_4571_,
                            );
                        if leanh::lean_obj_tag(v___x_4581_) == 0 {
                            v_a_4582_ = leanh::lean_ctor_get(v___x_4581_, 0);
                            leanh::lean_inc(v_a_4582_);
                            leanh::lean_dec_ref_known(v___x_4581_, 1);
                            v___x_4583_ = 0;
                            v___x_4584_ = l_Lean_Core_instantiateValueLevelParams(
                                v_a_4582_,
                                v_us_4575_,
                                v___x_4583_,
                                v___y_4570_,
                                v___y_4571_,
                            );
                            leanh::lean_dec(v_a_4582_);
                            if leanh::lean_obj_tag(v___x_4584_) == 0 {
                                v_a_4585_ = leanh::lean_ctor_get(v___x_4584_, 0);
                                v_isSharedCheck_4600_ =
                                    (!leanh::lean_is_exclusive(v___x_4584_)) as u8;
                                if v_isSharedCheck_4600_ == 0 {
                                    v___x_4587_ = v___x_4584_;
                                    v_isShared_4588_ = v_isSharedCheck_4600_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4585_);
                                    leanh::lean_dec(v___x_4584_);
                                    v___x_4587_ = leanh::lean_box(0);
                                    v_isShared_4588_ = v_isSharedCheck_4600_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_4569_);
                                v_a_4601_ = leanh::lean_ctor_get(v___x_4584_, 0);
                                v_isSharedCheck_4608_ =
                                    (!leanh::lean_is_exclusive(v___x_4584_)) as u8;
                                if v_isSharedCheck_4608_ == 0 {
                                    v___x_4603_ = v___x_4584_;
                                    v_isShared_4604_ = v_isSharedCheck_4608_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4601_);
                                    leanh::lean_dec(v___x_4584_);
                                    v___x_4603_ = leanh::lean_box(0);
                                    v_isShared_4604_ = v_isSharedCheck_4608_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_us_4575_);
                            leanh::lean_dec_ref(v_e_4569_);
                            v_a_4609_ = leanh::lean_ctor_get(v___x_4581_, 0);
                            v_isSharedCheck_4616_ =
                                (!leanh::lean_is_exclusive(v___x_4581_)) as u8;
                            if v_isSharedCheck_4616_ == 0 {
                                v___x_4611_ = v___x_4581_;
                                v_isShared_4612_ = v_isSharedCheck_4616_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4609_);
                                leanh::lean_dec(v___x_4581_);
                                v___x_4611_ = leanh::lean_box(0);
                                v_isShared_4612_ = v_isSharedCheck_4616_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4573_);
                    leanh::lean_dec_ref(v_e_4569_);
                    v___x_4617_ = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
                    v___x_4618_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4618_, 0, v___x_4617_);
                    return v___x_4618_;
                }
            }
            1 => {
                v_dummy_4589_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1,
                );
                v_nargs_4590_ = l_Lean_Expr_getAppNumArgs(v_e_4569_);
                leanh::lean_inc(v_nargs_4590_);
                v___x_4591_ = lean_mk_array(v_nargs_4590_, v_dummy_4589_);
                v___x_4592_ = leanh::lean_unsigned_to_nat(1);
                v___x_4593_ = lean_nat_sub(v_nargs_4590_, v___x_4592_);
                leanh::lean_dec(v_nargs_4590_);
                v___x_4594_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4569_,
                    v___x_4591_,
                    v___x_4593_,
                );
                v___x_4595_ = l_Lean_Expr_beta(v_a_4585_, v___x_4594_);
                v___x_4596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4596_, 0, v___x_4595_);
                if v_isShared_4588_ == 0 {
                    leanh::lean_ctor_set(v___x_4587_, 0, v___x_4596_);
                    v___x_4598_ = v___x_4587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
                    v___x_4598_ = v_reuseFailAlloc_4599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4598_;
            }
            3 => {
                if v_isShared_4604_ == 0 {
                    v___x_4606_ = v___x_4603_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4607_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
                    v___x_4606_ = v_reuseFailAlloc_4607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4606_;
            }
            5 => {
                if v_isShared_4612_ == 0 {
                    v___x_4614_ = v___x_4611_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4609_);
                    v___x_4614_ = v_reuseFailAlloc_4615_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_macroInline___lam__1___boxed(
    mut v_e_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ = l_Lean_Compiler_LCNF_macroInline___lam__1(v_e_4619_, v___y_4620_, v___y_4621_);
    leanh::lean_dec(v___y_4621_);
    leanh::lean_dec_ref(v___y_4620_);
    return v_res_4623_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ = leanh::lean_box(0);
    v___x_4625_ = l_Lean_interruptExceptionId;
    v___x_4626_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4626_, 0, v___x_4625_);
    leanh::lean_ctor_set(v___x_4626_, 1, v___x_4624_);
    return v___x_4626_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___closed__0);
    v___x_4629_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg___boxed(
    mut v___y_4630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4631_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg();
    return v_res_4631_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4638_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4638_, 0, v___x_4637_);
    return v___x_4638_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4639_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__3);
    v___x_4640_ = l_Lean_MessageData_ofFormat(v___x_4639_);
    return v___x_4640_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__4);
    v___x_4642_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__2;
    v___x_4643_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4643_, 0, v___x_4642_);
    leanh::lean_ctor_set(v___x_4643_, 1, v___x_4641_);
    return v___x_4643_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg(
    mut v_ref_4644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4646_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5);
    v___x_4647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4647_, 0, v_ref_4644_);
    leanh::lean_ctor_set(v___x_4647_, 1, v___x_4646_);
    v___x_4648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4648_, 0, v___x_4647_);
    return v___x_4648_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___boxed(
    mut v_ref_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4651_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg(v_ref_4649_);
    return v_res_4651_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8___redArg(
    mut v_x_4652_: *mut leanh::LeanObject,
    mut v___y_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4662_: u8 = 0;
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4666_: u8 = 0;
    let mut v___y_4668_: u8 = 0;
    let mut v___y_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4682_: u8 = 0;
    let mut v___y_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4700_: u8 = 0;
    let mut v_cancelTk_x3f_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4702_: u8 = 0;
    let mut v_inheritedTraceOptions_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: u8 = 0;
    let mut v___x_4707_: u8 = 0;
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: u8 = 0;
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4688_ = leanh::lean_ctor_get(v___y_4654_, 0);
                v_fileMap_4689_ = leanh::lean_ctor_get(v___y_4654_, 1);
                v_options_4690_ = leanh::lean_ctor_get(v___y_4654_, 2);
                v_currRecDepth_4691_ = leanh::lean_ctor_get(v___y_4654_, 3);
                v_maxRecDepth_4692_ = leanh::lean_ctor_get(v___y_4654_, 4);
                v_ref_4693_ = leanh::lean_ctor_get(v___y_4654_, 5);
                v_currNamespace_4694_ = leanh::lean_ctor_get(v___y_4654_, 6);
                v_openDecls_4695_ = leanh::lean_ctor_get(v___y_4654_, 7);
                v_initHeartbeats_4696_ = leanh::lean_ctor_get(v___y_4654_, 8);
                v_maxHeartbeats_4697_ = leanh::lean_ctor_get(v___y_4654_, 9);
                v_quotContext_4698_ = leanh::lean_ctor_get(v___y_4654_, 10);
                v_currMacroScope_4699_ = leanh::lean_ctor_get(v___y_4654_, 11);
                v_diag_4700_ = leanh::lean_ctor_get_uint8(
                    v___y_4654_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4701_ = leanh::lean_ctor_get(v___y_4654_, 12);
                v_suppressElabErrors_4702_ = leanh::lean_ctor_get_uint8(
                    v___y_4654_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4703_ = leanh::lean_ctor_get(v___y_4654_, 13);
                if leanh::lean_obj_tag(v_cancelTk_x3f_4701_) == 1 {
                    v_val_4709_ = leanh::lean_ctor_get(v_cancelTk_x3f_4701_, 0);
                    v___x_4710_ = l_IO_CancelToken_isSet(v_val_4709_);
                    if v___x_4710_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_4652_);
                        v___x_4711_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg();
                        v_a_4712_ = leanh::lean_ctor_get(v___x_4711_, 0);
                        v_isSharedCheck_4719_ =
                            (!leanh::lean_is_exclusive(v___x_4711_)) as u8;
                        if v_isSharedCheck_4719_ == 0 {
                            v___x_4714_ = v___x_4711_;
                            v_isShared_4715_ = v_isSharedCheck_4719_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4712_);
                            leanh::lean_dec(v___x_4711_);
                            v___x_4714_ = leanh::lean_box(0);
                            v_isShared_4715_ = v_isSharedCheck_4719_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4658_) == 0 {
                    return v___y_4658_;
                } else {
                    v_a_4659_ = leanh::lean_ctor_get(v___y_4658_, 0);
                    v_isSharedCheck_4666_ = (!leanh::lean_is_exclusive(v___y_4658_)) as u8;
                    if v_isSharedCheck_4666_ == 0 {
                        v___x_4661_ = v___y_4658_;
                        v_isShared_4662_ = v_isSharedCheck_4666_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4659_);
                        leanh::lean_dec(v___y_4658_);
                        v___x_4661_ = leanh::lean_box(0);
                        v_isShared_4662_ = v_isSharedCheck_4666_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4662_ == 0 {
                    v___x_4664_ = v___x_4661_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
                    v___x_4664_ = v_reuseFailAlloc_4665_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4664_;
            }
            4 => {
                v___x_4684_ = leanh::lean_unsigned_to_nat(1);
                v___x_4685_ = lean_nat_add(v___y_4679_, v___x_4684_);
                leanh::lean_inc_ref(v___y_4678_);
                leanh::lean_inc(v___y_4671_);
                leanh::lean_inc(v___y_4670_);
                leanh::lean_inc(v___y_4676_);
                leanh::lean_inc(v___y_4673_);
                leanh::lean_inc(v___y_4672_);
                leanh::lean_inc(v___y_4675_);
                leanh::lean_inc(v___y_4681_);
                leanh::lean_inc(v___y_4683_);
                leanh::lean_inc_ref(v___y_4677_);
                leanh::lean_inc_ref(v___y_4674_);
                leanh::lean_inc_ref(v___y_4680_);
                v___x_4686_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_4686_, 0, v___y_4680_);
                leanh::lean_ctor_set(v___x_4686_, 1, v___y_4674_);
                leanh::lean_ctor_set(v___x_4686_, 2, v___y_4677_);
                leanh::lean_ctor_set(v___x_4686_, 3, v___x_4685_);
                leanh::lean_ctor_set(v___x_4686_, 4, v___y_4683_);
                leanh::lean_ctor_set(v___x_4686_, 5, v___y_4669_);
                leanh::lean_ctor_set(v___x_4686_, 6, v___y_4681_);
                leanh::lean_ctor_set(v___x_4686_, 7, v___y_4675_);
                leanh::lean_ctor_set(v___x_4686_, 8, v___y_4672_);
                leanh::lean_ctor_set(v___x_4686_, 9, v___y_4673_);
                leanh::lean_ctor_set(v___x_4686_, 10, v___y_4676_);
                leanh::lean_ctor_set(v___x_4686_, 11, v___y_4670_);
                leanh::lean_ctor_set(v___x_4686_, 12, v___y_4671_);
                leanh::lean_ctor_set(v___x_4686_, 13, v___y_4678_);
                leanh::lean_ctor_set_uint8(
                    v___x_4686_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_4682_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4686_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_4668_,
                );
                leanh::lean_inc(v___y_4655_);
                leanh::lean_inc(v___y_4653_);
                v___x_4687_ = leanh::lean_apply_4(
                    v_x_4652_,
                    v___y_4653_,
                    v___x_4686_,
                    v___y_4655_,
                    leanh::lean_box(0),
                );
                v___y_4658_ = v___x_4687_;
                state = 1;
                continue;
            }
            5 => {
                v___x_4705_ = leanh::lean_unsigned_to_nat(0);
                v___x_4706_ = lean_nat_dec_eq(v_maxRecDepth_4692_, v___x_4705_);
                if v___x_4706_ == 0 {
                    v___x_4707_ = lean_nat_dec_eq(v_currRecDepth_4691_, v_maxRecDepth_4692_);
                    if v___x_4707_ == 0 {
                        leanh::lean_inc(v_ref_4693_);
                        v___y_4668_ = v_suppressElabErrors_4702_;
                        v___y_4669_ = v_ref_4693_;
                        v___y_4670_ = v_currMacroScope_4699_;
                        v___y_4671_ = v_cancelTk_x3f_4701_;
                        v___y_4672_ = v_initHeartbeats_4696_;
                        v___y_4673_ = v_maxHeartbeats_4697_;
                        v___y_4674_ = v_fileMap_4689_;
                        v___y_4675_ = v_openDecls_4695_;
                        v___y_4676_ = v_quotContext_4698_;
                        v___y_4677_ = v_options_4690_;
                        v___y_4678_ = v_inheritedTraceOptions_4703_;
                        v___y_4679_ = v_currRecDepth_4691_;
                        v___y_4680_ = v_fileName_4688_;
                        v___y_4681_ = v_currNamespace_4694_;
                        v___y_4682_ = v_diag_4700_;
                        v___y_4683_ = v_maxRecDepth_4692_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_4652_);
                        leanh::lean_inc(v_ref_4693_);
                        v___x_4708_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg(v_ref_4693_);
                        v___y_4658_ = v___x_4708_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_ref_4693_);
                    v___y_4668_ = v_suppressElabErrors_4702_;
                    v___y_4669_ = v_ref_4693_;
                    v___y_4670_ = v_currMacroScope_4699_;
                    v___y_4671_ = v_cancelTk_x3f_4701_;
                    v___y_4672_ = v_initHeartbeats_4696_;
                    v___y_4673_ = v_maxHeartbeats_4697_;
                    v___y_4674_ = v_fileMap_4689_;
                    v___y_4675_ = v_openDecls_4695_;
                    v___y_4676_ = v_quotContext_4698_;
                    v___y_4677_ = v_options_4690_;
                    v___y_4678_ = v_inheritedTraceOptions_4703_;
                    v___y_4679_ = v_currRecDepth_4691_;
                    v___y_4680_ = v_fileName_4688_;
                    v___y_4681_ = v_currNamespace_4694_;
                    v___y_4682_ = v_diag_4700_;
                    v___y_4683_ = v_maxRecDepth_4692_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_4715_ == 0 {
                    v___x_4717_ = v___x_4714_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4718_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
                    v___x_4717_ = v_reuseFailAlloc_4718_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8___redArg___boxed(
    mut v_x_4720_: *mut leanh::LeanObject,
    mut v___y_4721_: *mut leanh::LeanObject,
    mut v___y_4722_: *mut leanh::LeanObject,
    mut v___y_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4725_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8___redArg(v_x_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
    leanh::lean_dec(v___y_4723_);
    leanh::lean_dec_ref(v___y_4722_);
    leanh::lean_dec(v___y_4721_);
    return v_res_4725_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8___redArg(
    mut v_a_4726_: *mut leanh::LeanObject,
    mut v_x_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: u8 = 0;
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4727_) == 0 {
                    v___x_4728_ = leanh::lean_box(0);
                    return v___x_4728_;
                } else {
                    v_key_4729_ = leanh::lean_ctor_get(v_x_4727_, 0);
                    v_value_4730_ = leanh::lean_ctor_get(v_x_4727_, 1);
                    v_tail_4731_ = leanh::lean_ctor_get(v_x_4727_, 2);
                    v___x_4732_ = l_Lean_ExprStructEq_beq(v_key_4729_, v_a_4726_);
                    if v___x_4732_ == 0 {
                        v_x_4727_ = v_tail_4731_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4730_);
                        v___x_4734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4734_, 0, v_value_4730_);
                        return v___x_4734_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8___redArg___boxed(
    mut v_a_4735_: *mut leanh::LeanObject,
    mut v_x_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4737_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8___redArg(v_a_4735_, v_x_4736_);
    leanh::lean_dec(v_x_4736_);
    leanh::lean_dec_ref(v_a_4735_);
    return v_res_4737_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___redArg(
    mut v_m_4738_: *mut leanh::LeanObject,
    mut v_a_4739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: u64 = 0;
    let mut v___x_4743_: u64 = 0;
    let mut v___x_4744_: u64 = 0;
    let mut v_fold_4745_: u64 = 0;
    let mut v___x_4746_: u64 = 0;
    let mut v___x_4747_: u64 = 0;
    let mut v___x_4748_: u64 = 0;
    let mut v___x_4749_: usize = 0;
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: usize = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_4740_ = leanh::lean_ctor_get(v_m_4738_, 1);
    v___x_4741_ = lean_array_get_size(v_buckets_4740_);
    v___x_4742_ = l_Lean_ExprStructEq_hash(v_a_4739_);
    v___x_4743_ = 32u64;
    v___x_4744_ = lean_uint64_shift_right(v___x_4742_, v___x_4743_);
    v_fold_4745_ = lean_uint64_xor(v___x_4742_, v___x_4744_);
    v___x_4746_ = 16u64;
    v___x_4747_ = lean_uint64_shift_right(v_fold_4745_, v___x_4746_);
    v___x_4748_ = lean_uint64_xor(v_fold_4745_, v___x_4747_);
    v___x_4749_ = lean_uint64_to_usize(v___x_4748_);
    v___x_4750_ = lean_usize_of_nat(v___x_4741_);
    v___x_4751_ = 1usize;
    v___x_4752_ = lean_usize_sub(v___x_4750_, v___x_4751_);
    v___x_4753_ = lean_usize_land(v___x_4749_, v___x_4752_);
    v___x_4754_ = lean_array_uget_borrowed(v_buckets_4740_, v___x_4753_);
    v___x_4755_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8___redArg(v_a_4739_, v___x_4754_);
    return v___x_4755_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___redArg___boxed(
    mut v_m_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___redArg(v_m_4756_, v_a_4757_);
    leanh::lean_dec_ref(v_a_4757_);
    leanh::lean_dec_ref(v_m_4756_);
    return v_res_4758_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__0(
    mut v_00_u03b1_4759_: *mut leanh::LeanObject,
    mut v_x_4760_: *mut leanh::LeanObject,
    mut v___y_4761_: *mut leanh::LeanObject,
    mut v___y_4762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4764_ = leanh::lean_apply_1(v_x_4760_, leanh::lean_box(0));
    v___x_4765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4765_, 0, v___x_4764_);
    return v___x_4765_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__0___boxed(
    mut v_00_u03b1_4766_: *mut leanh::LeanObject,
    mut v_x_4767_: *mut leanh::LeanObject,
    mut v___y_4768_: *mut leanh::LeanObject,
    mut v___y_4769_: *mut leanh::LeanObject,
    mut v___y_4770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4771_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__0(v_00_u03b1_4766_, v_x_4767_, v___y_4768_, v___y_4769_);
    leanh::lean_dec(v___y_4769_);
    leanh::lean_dec_ref(v___y_4768_);
    return v_res_4771_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18_spec__21___redArg(
    mut v_x_4772_: *mut leanh::LeanObject,
    mut v_x_4773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4779_: u8 = 0;
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: u64 = 0;
    let mut v___x_4782_: u64 = 0;
    let mut v___x_4783_: u64 = 0;
    let mut v_fold_4784_: u64 = 0;
    let mut v___x_4785_: u64 = 0;
    let mut v___x_4786_: u64 = 0;
    let mut v___x_4787_: u64 = 0;
    let mut v___x_4788_: usize = 0;
    let mut v___x_4789_: usize = 0;
    let mut v___x_4790_: usize = 0;
    let mut v___x_4791_: usize = 0;
    let mut v___x_4792_: usize = 0;
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4773_) == 0 {
                    return v_x_4772_;
                } else {
                    v_key_4774_ = leanh::lean_ctor_get(v_x_4773_, 0);
                    v_value_4775_ = leanh::lean_ctor_get(v_x_4773_, 1);
                    v_tail_4776_ = leanh::lean_ctor_get(v_x_4773_, 2);
                    v_isSharedCheck_4799_ = (!leanh::lean_is_exclusive(v_x_4773_)) as u8;
                    if v_isSharedCheck_4799_ == 0 {
                        v___x_4778_ = v_x_4773_;
                        v_isShared_4779_ = v_isSharedCheck_4799_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4776_);
                        leanh::lean_inc(v_value_4775_);
                        leanh::lean_inc(v_key_4774_);
                        leanh::lean_dec(v_x_4773_);
                        v___x_4778_ = leanh::lean_box(0);
                        v_isShared_4779_ = v_isSharedCheck_4799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4780_ = lean_array_get_size(v_x_4772_);
                v___x_4781_ = l_Lean_ExprStructEq_hash(v_key_4774_);
                v___x_4782_ = 32u64;
                v___x_4783_ = lean_uint64_shift_right(v___x_4781_, v___x_4782_);
                v_fold_4784_ = lean_uint64_xor(v___x_4781_, v___x_4783_);
                v___x_4785_ = 16u64;
                v___x_4786_ = lean_uint64_shift_right(v_fold_4784_, v___x_4785_);
                v___x_4787_ = lean_uint64_xor(v_fold_4784_, v___x_4786_);
                v___x_4788_ = lean_uint64_to_usize(v___x_4787_);
                v___x_4789_ = lean_usize_of_nat(v___x_4780_);
                v___x_4790_ = 1usize;
                v___x_4791_ = lean_usize_sub(v___x_4789_, v___x_4790_);
                v___x_4792_ = lean_usize_land(v___x_4788_, v___x_4791_);
                v___x_4793_ = lean_array_uget_borrowed(v_x_4772_, v___x_4792_);
                leanh::lean_inc(v___x_4793_);
                if v_isShared_4779_ == 0 {
                    leanh::lean_ctor_set(v___x_4778_, 2, v___x_4793_);
                    v___x_4795_ = v___x_4778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_key_4774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_value_4775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 2, v___x_4793_);
                    v___x_4795_ = v_reuseFailAlloc_4798_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4796_ = lean_array_uset(v_x_4772_, v___x_4792_, v___x_4795_);
                v_x_4772_ = v___x_4796_;
                v_x_4773_ = v_tail_4776_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18___redArg(
    mut v_i_4800_: *mut leanh::LeanObject,
    mut v_source_4801_: *mut leanh::LeanObject,
    mut v_target_4802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: u8 = 0;
    let mut v_es_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4803_ = lean_array_get_size(v_source_4801_);
                v___x_4804_ = lean_nat_dec_lt(v_i_4800_, v___x_4803_);
                if v___x_4804_ == 0 {
                    leanh::lean_dec_ref(v_source_4801_);
                    leanh::lean_dec(v_i_4800_);
                    return v_target_4802_;
                } else {
                    v_es_4805_ = lean_array_fget(v_source_4801_, v_i_4800_);
                    v___x_4806_ = leanh::lean_box(0);
                    v_source_4807_ = lean_array_fset(v_source_4801_, v_i_4800_, v___x_4806_);
                    v_target_4808_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18_spec__21___redArg(v_target_4802_, v_es_4805_);
                    v___x_4809_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4810_ = lean_nat_add(v_i_4800_, v___x_4809_);
                    leanh::lean_dec(v_i_4800_);
                    v_i_4800_ = v___x_4810_;
                    v_source_4801_ = v_source_4807_;
                    v_target_4802_ = v_target_4808_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15___redArg(
    mut v_data_4812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4813_ = lean_array_get_size(v_data_4812_);
    v___x_4814_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4815_ = lean_nat_mul(v___x_4813_, v___x_4814_);
    v___x_4816_ = leanh::lean_unsigned_to_nat(0);
    v___x_4817_ = leanh::lean_box(0);
    v___x_4818_ = lean_mk_array(v_nbuckets_4815_, v___x_4817_);
    v___x_4819_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18___redArg(v___x_4816_, v_data_4812_, v___x_4818_);
    return v___x_4819_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__16___redArg(
    mut v_a_4820_: *mut leanh::LeanObject,
    mut v_b_4821_: *mut leanh::LeanObject,
    mut v_x_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4828_: u8 = 0;
    let mut v___x_4829_: u8 = 0;
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4822_) == 0 {
                    leanh::lean_dec(v_b_4821_);
                    leanh::lean_dec_ref(v_a_4820_);
                    return v_x_4822_;
                } else {
                    v_key_4823_ = leanh::lean_ctor_get(v_x_4822_, 0);
                    v_value_4824_ = leanh::lean_ctor_get(v_x_4822_, 1);
                    v_tail_4825_ = leanh::lean_ctor_get(v_x_4822_, 2);
                    v_isSharedCheck_4837_ = (!leanh::lean_is_exclusive(v_x_4822_)) as u8;
                    if v_isSharedCheck_4837_ == 0 {
                        v___x_4827_ = v_x_4822_;
                        v_isShared_4828_ = v_isSharedCheck_4837_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4825_);
                        leanh::lean_inc(v_value_4824_);
                        leanh::lean_inc(v_key_4823_);
                        leanh::lean_dec(v_x_4822_);
                        v___x_4827_ = leanh::lean_box(0);
                        v_isShared_4828_ = v_isSharedCheck_4837_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4829_ = l_Lean_ExprStructEq_beq(v_key_4823_, v_a_4820_);
                if v___x_4829_ == 0 {
                    v___x_4830_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__16___redArg(v_a_4820_, v_b_4821_, v_tail_4825_);
                    if v_isShared_4828_ == 0 {
                        leanh::lean_ctor_set(v___x_4827_, 2, v___x_4830_);
                        v___x_4832_ = v___x_4827_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4833_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_key_4823_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4833_, 1, v_value_4824_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4833_, 2, v___x_4830_);
                        v___x_4832_ = v_reuseFailAlloc_4833_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_4824_);
                    leanh::lean_dec(v_key_4823_);
                    if v_isShared_4828_ == 0 {
                        leanh::lean_ctor_set(v___x_4827_, 1, v_b_4821_);
                        leanh::lean_ctor_set(v___x_4827_, 0, v_a_4820_);
                        v___x_4835_ = v___x_4827_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4836_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4820_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4836_, 1, v_b_4821_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4836_, 2, v_tail_4825_);
                        v___x_4835_ = v_reuseFailAlloc_4836_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4832_;
            }
            3 => {
                return v___x_4835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14___redArg(
    mut v_a_4838_: *mut leanh::LeanObject,
    mut v_x_4839_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4840_: u8 = 0;
    let mut v_key_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4839_) == 0 {
                    v___x_4840_ = 0;
                    return v___x_4840_;
                } else {
                    v_key_4841_ = leanh::lean_ctor_get(v_x_4839_, 0);
                    v_tail_4842_ = leanh::lean_ctor_get(v_x_4839_, 2);
                    v___x_4843_ = l_Lean_ExprStructEq_beq(v_key_4841_, v_a_4838_);
                    if v___x_4843_ == 0 {
                        v_x_4839_ = v_tail_4842_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4843_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14___redArg___boxed(
    mut v_a_4845_: *mut leanh::LeanObject,
    mut v_x_4846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4847_: u8 = 0;
    let mut v_r_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14___redArg(v_a_4845_, v_x_4846_);
    leanh::lean_dec(v_x_4846_);
    leanh::lean_dec_ref(v_a_4845_);
    v_r_4848_ = leanh::lean_box((v_res_4847_) as usize);
    return v_r_4848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9___redArg(
    mut v_m_4849_: *mut leanh::LeanObject,
    mut v_a_4850_: *mut leanh::LeanObject,
    mut v_b_4851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4856_: u8 = 0;
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: u64 = 0;
    let mut v___x_4859_: u64 = 0;
    let mut v___x_4860_: u64 = 0;
    let mut v_fold_4861_: u64 = 0;
    let mut v___x_4862_: u64 = 0;
    let mut v___x_4863_: u64 = 0;
    let mut v___x_4864_: u64 = 0;
    let mut v___x_4865_: usize = 0;
    let mut v___x_4866_: usize = 0;
    let mut v___x_4867_: usize = 0;
    let mut v___x_4868_: usize = 0;
    let mut v___x_4869_: usize = 0;
    let mut v_bkt_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: u8 = 0;
    let mut v_val_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4852_ = leanh::lean_ctor_get(v_m_4849_, 0);
                v_buckets_4853_ = leanh::lean_ctor_get(v_m_4849_, 1);
                v_isSharedCheck_4896_ = (!leanh::lean_is_exclusive(v_m_4849_)) as u8;
                if v_isSharedCheck_4896_ == 0 {
                    v___x_4855_ = v_m_4849_;
                    v_isShared_4856_ = v_isSharedCheck_4896_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4853_);
                    leanh::lean_inc(v_size_4852_);
                    leanh::lean_dec(v_m_4849_);
                    v___x_4855_ = leanh::lean_box(0);
                    v_isShared_4856_ = v_isSharedCheck_4896_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4857_ = lean_array_get_size(v_buckets_4853_);
                v___x_4858_ = l_Lean_ExprStructEq_hash(v_a_4850_);
                v___x_4859_ = 32u64;
                v___x_4860_ = lean_uint64_shift_right(v___x_4858_, v___x_4859_);
                v_fold_4861_ = lean_uint64_xor(v___x_4858_, v___x_4860_);
                v___x_4862_ = 16u64;
                v___x_4863_ = lean_uint64_shift_right(v_fold_4861_, v___x_4862_);
                v___x_4864_ = lean_uint64_xor(v_fold_4861_, v___x_4863_);
                v___x_4865_ = lean_uint64_to_usize(v___x_4864_);
                v___x_4866_ = lean_usize_of_nat(v___x_4857_);
                v___x_4867_ = 1usize;
                v___x_4868_ = lean_usize_sub(v___x_4866_, v___x_4867_);
                v___x_4869_ = lean_usize_land(v___x_4865_, v___x_4868_);
                v_bkt_4870_ = lean_array_uget_borrowed(v_buckets_4853_, v___x_4869_);
                v___x_4871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14___redArg(v_a_4850_, v_bkt_4870_);
                if v___x_4871_ == 0 {
                    v___x_4872_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4873_ = lean_nat_add(v_size_4852_, v___x_4872_);
                    leanh::lean_dec(v_size_4852_);
                    leanh::lean_inc(v_bkt_4870_);
                    v___x_4874_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4874_, 0, v_a_4850_);
                    leanh::lean_ctor_set(v___x_4874_, 1, v_b_4851_);
                    leanh::lean_ctor_set(v___x_4874_, 2, v_bkt_4870_);
                    v_buckets_x27_4875_ =
                        lean_array_uset(v_buckets_4853_, v___x_4869_, v___x_4874_);
                    v___x_4876_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4877_ = lean_nat_mul(v_size_x27_4873_, v___x_4876_);
                    v___x_4878_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4879_ = lean_nat_div(v___x_4877_, v___x_4878_);
                    leanh::lean_dec(v___x_4877_);
                    v___x_4880_ = lean_array_get_size(v_buckets_x27_4875_);
                    v___x_4881_ = lean_nat_dec_le(v___x_4879_, v___x_4880_);
                    leanh::lean_dec(v___x_4879_);
                    if v___x_4881_ == 0 {
                        v_val_4882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15___redArg(v_buckets_x27_4875_);
                        if v_isShared_4856_ == 0 {
                            leanh::lean_ctor_set(v___x_4855_, 1, v_val_4882_);
                            leanh::lean_ctor_set(v___x_4855_, 0, v_size_x27_4873_);
                            v___x_4884_ = v___x_4855_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4885_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4885_,
                                0,
                                v_size_x27_4873_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_val_4882_);
                            v___x_4884_ = v_reuseFailAlloc_4885_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4856_ == 0 {
                            leanh::lean_ctor_set(v___x_4855_, 1, v_buckets_x27_4875_);
                            leanh::lean_ctor_set(v___x_4855_, 0, v_size_x27_4873_);
                            v___x_4887_ = v___x_4855_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4888_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4888_,
                                0,
                                v_size_x27_4873_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4888_,
                                1,
                                v_buckets_x27_4875_,
                            );
                            v___x_4887_ = v_reuseFailAlloc_4888_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_4870_);
                    v___x_4889_ = leanh::lean_box(0);
                    v_buckets_x27_4890_ =
                        lean_array_uset(v_buckets_4853_, v___x_4869_, v___x_4889_);
                    v___x_4891_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__16___redArg(v_a_4850_, v_b_4851_, v_bkt_4870_);
                    v___x_4892_ = lean_array_uset(v_buckets_x27_4890_, v___x_4869_, v___x_4891_);
                    if v_isShared_4856_ == 0 {
                        leanh::lean_ctor_set(v___x_4855_, 1, v___x_4892_);
                        v___x_4894_ = v___x_4855_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_size_4852_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 1, v___x_4892_);
                        v___x_4894_ = v_reuseFailAlloc_4895_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4884_;
            }
            3 => {
                return v___x_4887_;
            }
            4 => {
                return v___x_4894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__2(
    mut v_a_4897_: *mut leanh::LeanObject,
    mut v_e_4898_: *mut leanh::LeanObject,
    mut v_a_4899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = lean_st_ref_take(v_a_4897_);
    v___x_4902_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9___redArg(v___x_4901_, v_e_4898_, v_a_4899_);
    v___x_4903_ = lean_st_ref_set(v_a_4897_, v___x_4902_);
    v___x_4904_ = leanh::lean_box(0);
    return v___x_4904_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__2___boxed(
    mut v_a_4905_: *mut leanh::LeanObject,
    mut v_e_4906_: *mut leanh::LeanObject,
    mut v_a_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4909_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__2(v_a_4905_, v_e_4906_, v_a_4907_);
    leanh::lean_dec(v_a_4905_);
    return v_res_4909_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__4(
    mut v_pre_4911_: *mut leanh::LeanObject,
    mut v_post_4912_: *mut leanh::LeanObject,
    mut v_sz_4913_: usize,
    mut v_i_4914_: usize,
    mut v_bs_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___y_4918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: usize = 0;
    let mut v___x_4928_: usize = 0;
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4920_ = lean_usize_dec_lt(v_i_4914_, v_sz_4913_);
                if v___x_4920_ == 0 {
                    leanh::lean_dec_ref(v_post_4912_);
                    leanh::lean_dec_ref(v_pre_4911_);
                    v___x_4921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4921_, 0, v_bs_4915_);
                    return v___x_4921_;
                } else {
                    v_v_4922_ = lean_array_uget_borrowed(v_bs_4915_, v_i_4914_);
                    leanh::lean_inc(v_v_4922_);
                    leanh::lean_inc_ref(v_post_4912_);
                    leanh::lean_inc_ref(v_pre_4911_);
                    v___x_4923_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4911_, v_post_4912_, v_v_4922_, v___y_4916_, v___y_4917_, v___y_4918_);
                    if leanh::lean_obj_tag(v___x_4923_) == 0 {
                        v_a_4924_ = leanh::lean_ctor_get(v___x_4923_, 0);
                        leanh::lean_inc(v_a_4924_);
                        leanh::lean_dec_ref_known(v___x_4923_, 1);
                        v___x_4925_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4926_ = lean_array_uset(v_bs_4915_, v_i_4914_, v___x_4925_);
                        v___x_4927_ = 1usize;
                        v___x_4928_ = lean_usize_add(v_i_4914_, v___x_4927_);
                        v___x_4929_ = lean_array_uset(v_bs_x27_4926_, v_i_4914_, v_a_4924_);
                        v_i_4914_ = v___x_4928_;
                        v_bs_4915_ = v___x_4929_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4915_);
                        leanh::lean_dec_ref(v_post_4912_);
                        leanh::lean_dec_ref(v_pre_4911_);
                        v_a_4931_ = leanh::lean_ctor_get(v___x_4923_, 0);
                        v_isSharedCheck_4938_ =
                            (!leanh::lean_is_exclusive(v___x_4923_)) as u8;
                        if v_isSharedCheck_4938_ == 0 {
                            v___x_4933_ = v___x_4923_;
                            v_isShared_4934_ = v_isSharedCheck_4938_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4931_);
                            leanh::lean_dec(v___x_4923_);
                            v___x_4933_ = leanh::lean_box(0);
                            v_isShared_4934_ = v_isSharedCheck_4938_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4934_ == 0 {
                    v___x_4936_ = v___x_4933_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__7(
    mut v_pre_4939_: *mut leanh::LeanObject,
    mut v_post_4940_: *mut leanh::LeanObject,
    mut v_x_4941_: *mut leanh::LeanObject,
    mut v_x_4942_: *mut leanh::LeanObject,
    mut v_x_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4956_: usize = 0;
    let mut v___x_4957_: usize = 0;
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4941_) == 5 {
                    v_fn_4948_ = leanh::lean_ctor_get(v_x_4941_, 0);
                    leanh::lean_inc_ref(v_fn_4948_);
                    v_arg_4949_ = leanh::lean_ctor_get(v_x_4941_, 1);
                    leanh::lean_inc_ref(v_arg_4949_);
                    leanh::lean_dec_ref_known(v_x_4941_, 2);
                    v___x_4950_ = lean_array_set(v_x_4942_, v_x_4943_, v_arg_4949_);
                    v___x_4951_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4952_ = lean_nat_sub(v_x_4943_, v___x_4951_);
                    leanh::lean_dec(v_x_4943_);
                    v_x_4941_ = v_fn_4948_;
                    v_x_4942_ = v___x_4950_;
                    v_x_4943_ = v___x_4952_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_4943_);
                    leanh::lean_inc_ref(v_post_4940_);
                    leanh::lean_inc_ref(v_pre_4939_);
                    v___x_4954_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4939_, v_post_4940_, v_x_4941_, v___y_4944_, v___y_4945_, v___y_4946_);
                    if leanh::lean_obj_tag(v___x_4954_) == 0 {
                        v_a_4955_ = leanh::lean_ctor_get(v___x_4954_, 0);
                        leanh::lean_inc(v_a_4955_);
                        leanh::lean_dec_ref_known(v___x_4954_, 1);
                        v_sz_4956_ = lean_array_size(v_x_4942_);
                        v___x_4957_ = 0usize;
                        leanh::lean_inc_ref(v_post_4940_);
                        leanh::lean_inc_ref(v_pre_4939_);
                        v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__4(v_pre_4939_, v_post_4940_, v_sz_4956_, v___x_4957_, v_x_4942_, v___y_4944_, v___y_4945_, v___y_4946_);
                        if leanh::lean_obj_tag(v___x_4958_) == 0 {
                            v_a_4959_ = leanh::lean_ctor_get(v___x_4958_, 0);
                            leanh::lean_inc(v_a_4959_);
                            leanh::lean_dec_ref_known(v___x_4958_, 1);
                            v___x_4960_ = l_Lean_mkAppN(v_a_4955_, v_a_4959_);
                            leanh::lean_dec(v_a_4959_);
                            v___x_4961_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4939_, v_post_4940_, v___x_4960_, v___y_4944_, v___y_4945_, v___y_4946_);
                            return v___x_4961_;
                        } else {
                            leanh::lean_dec(v_a_4955_);
                            leanh::lean_dec_ref(v_post_4940_);
                            leanh::lean_dec_ref(v_pre_4939_);
                            v_a_4962_ = leanh::lean_ctor_get(v___x_4958_, 0);
                            v_isSharedCheck_4969_ =
                                (!leanh::lean_is_exclusive(v___x_4958_)) as u8;
                            if v_isSharedCheck_4969_ == 0 {
                                v___x_4964_ = v___x_4958_;
                                v_isShared_4965_ = v_isSharedCheck_4969_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4962_);
                                leanh::lean_dec(v___x_4958_);
                                v___x_4964_ = leanh::lean_box(0);
                                v_isShared_4965_ = v_isSharedCheck_4969_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_4942_);
                        leanh::lean_dec_ref(v_post_4940_);
                        leanh::lean_dec_ref(v_pre_4939_);
                        return v___x_4954_;
                    }
                }
            }
            1 => {
                if v_isShared_4965_ == 0 {
                    v___x_4967_ = v___x_4964_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4968_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
                    v___x_4967_ = v_reuseFailAlloc_4968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__1(
    mut v___x_4970_: *mut leanh::LeanObject,
    mut v_pre_4971_: *mut leanh::LeanObject,
    mut v_e_4972_: *mut leanh::LeanObject,
    mut v_post_4973_: *mut leanh::LeanObject,
    mut v___y_4974_: *mut leanh::LeanObject,
    mut v___y_4975_: *mut leanh::LeanObject,
    mut v___y_4976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4981_: u8 = 0;
    let mut v___y_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4986_: u8 = 0;
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: usize = 0;
    let mut v___x_4990_: usize = 0;
    let mut v___x_4991_: u8 = 0;
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4997_: u8 = 0;
    let mut v___y_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5001_: u8 = 0;
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: u8 = 0;
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5012_: u8 = 0;
    let mut v___y_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5014_: u8 = 0;
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5026_: u8 = 0;
    let mut v___y_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5032_: u8 = 0;
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: usize = 0;
    let mut v___x_5038_: usize = 0;
    let mut v___x_5039_: u8 = 0;
    let mut v___x_5040_: usize = 0;
    let mut v___x_5041_: usize = 0;
    let mut v___x_5042_: u8 = 0;
    let mut v_binderName_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5046_: u8 = 0;
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: usize = 0;
    let mut v___x_5052_: usize = 0;
    let mut v___x_5053_: u8 = 0;
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: usize = 0;
    let mut v___x_5056_: u8 = 0;
    let mut v_declName_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_5061_: u8 = 0;
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: usize = 0;
    let mut v___x_5069_: usize = 0;
    let mut v___x_5070_: u8 = 0;
    let mut v___x_5071_: usize = 0;
    let mut v___x_5072_: usize = 0;
    let mut v___x_5073_: u8 = 0;
    let mut v_dummy_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: usize = 0;
    let mut v___x_5085_: usize = 0;
    let mut v___x_5086_: u8 = 0;
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: usize = 0;
    let mut v___x_5096_: usize = 0;
    let mut v___x_5097_: u8 = 0;
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5112_: u8 = 0;
    let mut v_a_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5116_: u8 = 0;
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5120_: u8 = 0;
    let mut v_a_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5021_ = l_Lean_Core_checkSystem(v___x_4970_, v___y_4975_, v___y_4976_);
                if leanh::lean_obj_tag(v___x_5021_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5021_, 1);
                    leanh::lean_inc_ref(v_pre_4971_);
                    leanh::lean_inc(v___y_4976_);
                    leanh::lean_inc_ref(v___y_4975_);
                    leanh::lean_inc_ref(v_e_4972_);
                    v___x_5022_ = leanh::lean_apply_4(
                        v_pre_4971_,
                        v_e_4972_,
                        v___y_4975_,
                        v___y_4976_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_5022_) == 0 {
                        v_a_5023_ = leanh::lean_ctor_get(v___x_5022_, 0);
                        v_isSharedCheck_5112_ =
                            (!leanh::lean_is_exclusive(v___x_5022_)) as u8;
                        if v_isSharedCheck_5112_ == 0 {
                            v___x_5025_ = v___x_5022_;
                            v_isShared_5026_ = v_isSharedCheck_5112_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5023_);
                            leanh::lean_dec(v___x_5022_);
                            v___x_5025_ = leanh::lean_box(0);
                            v_isShared_5026_ = v_isSharedCheck_5112_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_e_4972_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        v_a_5113_ = leanh::lean_ctor_get(v___x_5022_, 0);
                        v_isSharedCheck_5120_ =
                            (!leanh::lean_is_exclusive(v___x_5022_)) as u8;
                        if v_isSharedCheck_5120_ == 0 {
                            v___x_5115_ = v___x_5022_;
                            v_isShared_5116_ = v_isSharedCheck_5120_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5113_);
                            leanh::lean_dec(v___x_5022_);
                            v___x_5115_ = leanh::lean_box(0);
                            v_isShared_5116_ = v_isSharedCheck_5120_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_4973_);
                    leanh::lean_dec_ref(v_e_4972_);
                    leanh::lean_dec_ref(v_pre_4971_);
                    v_a_5121_ = leanh::lean_ctor_get(v___x_5021_, 0);
                    v_isSharedCheck_5128_ = (!leanh::lean_is_exclusive(v___x_5021_)) as u8;
                    if v_isSharedCheck_5128_ == 0 {
                        v___x_5123_ = v___x_5021_;
                        v_isShared_5124_ = v_isSharedCheck_5128_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5121_);
                        leanh::lean_dec(v___x_5021_);
                        v___x_5123_ = leanh::lean_box(0);
                        v_isShared_5124_ = v_isSharedCheck_5128_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4986_ == 0 {
                    leanh::lean_dec_ref(v___y_4985_);
                    leanh::lean_dec_ref(v___y_4983_);
                    v___x_4987_ = l_Lean_Expr_letE___override(
                        v___y_4980_,
                        v___y_4984_,
                        v___y_4979_,
                        v___y_4982_,
                        v___y_4981_,
                    );
                    v___x_4988_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_4987_, v___y_4974_, v___y_4975_, v___y_4976_);
                    return v___x_4988_;
                } else {
                    v___x_4989_ = lean_ptr_addr(v___y_4985_);
                    leanh::lean_dec_ref(v___y_4985_);
                    v___x_4990_ = lean_ptr_addr(v___y_4982_);
                    v___x_4991_ = lean_usize_dec_eq(v___x_4989_, v___x_4990_);
                    if v___x_4991_ == 0 {
                        leanh::lean_dec_ref(v___y_4983_);
                        v___x_4992_ = l_Lean_Expr_letE___override(
                            v___y_4980_,
                            v___y_4984_,
                            v___y_4979_,
                            v___y_4982_,
                            v___y_4981_,
                        );
                        v___x_4993_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_4992_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_4993_;
                    } else {
                        leanh::lean_dec_ref(v___y_4984_);
                        leanh::lean_dec_ref(v___y_4982_);
                        leanh::lean_dec(v___y_4980_);
                        leanh::lean_dec_ref(v___y_4979_);
                        v___x_4994_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___y_4983_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_4994_;
                    }
                }
            }
            2 => {
                if v___y_5001_ == 0 {
                    leanh::lean_dec_ref(v___y_4996_);
                    v___x_5002_ = l_Lean_Expr_lam___override(
                        v___y_4998_,
                        v___y_5000_,
                        v___y_4999_,
                        v___y_4997_,
                    );
                    v___x_5003_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_5002_, v___y_4974_, v___y_4975_, v___y_4976_);
                    return v___x_5003_;
                } else {
                    v___x_5004_ = l_Lean_instBEqBinderInfo_beq(v___y_4997_, v___y_4997_);
                    if v___x_5004_ == 0 {
                        leanh::lean_dec_ref(v___y_4996_);
                        v___x_5005_ = l_Lean_Expr_lam___override(
                            v___y_4998_,
                            v___y_5000_,
                            v___y_4999_,
                            v___y_4997_,
                        );
                        v___x_5006_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_5005_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_5006_;
                    } else {
                        leanh::lean_dec_ref(v___y_5000_);
                        leanh::lean_dec_ref(v___y_4999_);
                        leanh::lean_dec(v___y_4998_);
                        v___x_5007_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___y_4996_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_5007_;
                    }
                }
            }
            3 => {
                if v___y_5014_ == 0 {
                    leanh::lean_dec_ref(v___y_5010_);
                    v___x_5015_ = l_Lean_Expr_forallE___override(
                        v___y_5011_,
                        v___y_5009_,
                        v___y_5013_,
                        v___y_5012_,
                    );
                    v___x_5016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_5015_, v___y_4974_, v___y_4975_, v___y_4976_);
                    return v___x_5016_;
                } else {
                    v___x_5017_ = l_Lean_instBEqBinderInfo_beq(v___y_5012_, v___y_5012_);
                    if v___x_5017_ == 0 {
                        leanh::lean_dec_ref(v___y_5010_);
                        v___x_5018_ = l_Lean_Expr_forallE___override(
                            v___y_5011_,
                            v___y_5009_,
                            v___y_5013_,
                            v___y_5012_,
                        );
                        v___x_5019_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_5018_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_5019_;
                    } else {
                        leanh::lean_dec_ref(v___y_5013_);
                        leanh::lean_dec(v___y_5011_);
                        leanh::lean_dec_ref(v___y_5009_);
                        v___x_5020_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___y_5010_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_5020_;
                    }
                }
            }
            4 => match leanh::lean_obj_tag(v_a_5023_) {
                0 => {
                    leanh::lean_dec_ref(v_post_4973_);
                    leanh::lean_dec_ref(v_e_4972_);
                    leanh::lean_dec_ref(v_pre_4971_);
                    v_e_5102_ = leanh::lean_ctor_get(v_a_5023_, 0);
                    leanh::lean_inc_ref(v_e_5102_);
                    leanh::lean_dec_ref_known(v_a_5023_, 1);
                    if v_isShared_5026_ == 0 {
                        leanh::lean_ctor_set(v___x_5025_, 0, v_e_5102_);
                        v___x_5104_ = v___x_5025_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_e_5102_);
                        v___x_5104_ = v_reuseFailAlloc_5105_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_5025_);
                    leanh::lean_dec_ref(v_e_4972_);
                    v_e_5106_ = leanh::lean_ctor_get(v_a_5023_, 0);
                    leanh::lean_inc_ref(v_e_5106_);
                    leanh::lean_dec_ref_known(v_a_5023_, 1);
                    leanh::lean_inc_ref(v_post_4973_);
                    leanh::lean_inc_ref(v_pre_4971_);
                    v___x_5107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_e_5106_, v___y_4974_, v___y_4975_, v___y_4976_);
                    if leanh::lean_obj_tag(v___x_5107_) == 0 {
                        v_a_5108_ = leanh::lean_ctor_get(v___x_5107_, 0);
                        leanh::lean_inc(v_a_5108_);
                        leanh::lean_dec_ref_known(v___x_5107_, 1);
                        v___x_5109_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v_a_5108_, v___y_4974_, v___y_4975_, v___y_4976_);
                        return v___x_5109_;
                    } else {
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        return v___x_5107_;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_5025_);
                    v_e_x3f_5110_ = leanh::lean_ctor_get(v_a_5023_, 0);
                    leanh::lean_inc(v_e_x3f_5110_);
                    leanh::lean_dec_ref_known(v_a_5023_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_5110_) == 0 {
                        v___y_5028_ = v_e_4972_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_4972_);
                        v_val_5111_ = leanh::lean_ctor_get(v_e_x3f_5110_, 0);
                        leanh::lean_inc(v_val_5111_);
                        leanh::lean_dec_ref_known(v_e_x3f_5110_, 1);
                        v___y_5028_ = v_val_5111_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match leanh::lean_obj_tag(v___y_5028_) {
                7 => {
                    v_binderName_5029_ = leanh::lean_ctor_get(v___y_5028_, 0);
                    leanh::lean_inc(v_binderName_5029_);
                    v_binderType_5030_ = leanh::lean_ctor_get(v___y_5028_, 1);
                    v_body_5031_ = leanh::lean_ctor_get(v___y_5028_, 2);
                    v_binderInfo_5032_ = leanh::lean_ctor_get_uint8(
                        v___y_5028_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_5030_);
                    leanh::lean_inc_ref(v_post_4973_);
                    leanh::lean_inc_ref(v_pre_4971_);
                    v___x_5033_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_binderType_5030_, v___y_4974_, v___y_4975_, v___y_4976_);
                    if leanh::lean_obj_tag(v___x_5033_) == 0 {
                        v_a_5034_ = leanh::lean_ctor_get(v___x_5033_, 0);
                        leanh::lean_inc(v_a_5034_);
                        leanh::lean_dec_ref_known(v___x_5033_, 1);
                        leanh::lean_inc_ref(v_body_5031_);
                        leanh::lean_inc_ref(v_post_4973_);
                        leanh::lean_inc_ref(v_pre_4971_);
                        v___x_5035_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_body_5031_, v___y_4974_, v___y_4975_, v___y_4976_);
                        if leanh::lean_obj_tag(v___x_5035_) == 0 {
                            v_a_5036_ = leanh::lean_ctor_get(v___x_5035_, 0);
                            leanh::lean_inc(v_a_5036_);
                            leanh::lean_dec_ref_known(v___x_5035_, 1);
                            v___x_5037_ = lean_ptr_addr(v_binderType_5030_);
                            v___x_5038_ = lean_ptr_addr(v_a_5034_);
                            v___x_5039_ = lean_usize_dec_eq(v___x_5037_, v___x_5038_);
                            if v___x_5039_ == 0 {
                                v___y_5009_ = v_a_5034_;
                                v___y_5010_ = v___y_5028_;
                                v___y_5011_ = v_binderName_5029_;
                                v___y_5012_ = v_binderInfo_5032_;
                                v___y_5013_ = v_a_5036_;
                                v___y_5014_ = v___x_5039_;
                                state = 3;
                                continue;
                            } else {
                                v___x_5040_ = lean_ptr_addr(v_body_5031_);
                                v___x_5041_ = lean_ptr_addr(v_a_5036_);
                                v___x_5042_ = lean_usize_dec_eq(v___x_5040_, v___x_5041_);
                                v___y_5009_ = v_a_5034_;
                                v___y_5010_ = v___y_5028_;
                                v___y_5011_ = v_binderName_5029_;
                                v___y_5012_ = v_binderInfo_5032_;
                                v___y_5013_ = v_a_5036_;
                                v___y_5014_ = v___x_5042_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5034_);
                            leanh::lean_dec(v_binderName_5029_);
                            leanh::lean_dec_ref_known(v___y_5028_, 3);
                            leanh::lean_dec_ref(v_post_4973_);
                            leanh::lean_dec_ref(v_pre_4971_);
                            return v___x_5035_;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_5029_);
                        leanh::lean_dec_ref_known(v___y_5028_, 3);
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        return v___x_5033_;
                    }
                }
                6 => {
                    v_binderName_5043_ = leanh::lean_ctor_get(v___y_5028_, 0);
                    leanh::lean_inc(v_binderName_5043_);
                    v_binderType_5044_ = leanh::lean_ctor_get(v___y_5028_, 1);
                    v_body_5045_ = leanh::lean_ctor_get(v___y_5028_, 2);
                    v_binderInfo_5046_ = leanh::lean_ctor_get_uint8(
                        v___y_5028_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_5044_);
                    leanh::lean_inc_ref(v_post_4973_);
                    leanh::lean_inc_ref(v_pre_4971_);
                    v___x_5047_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_binderType_5044_, v___y_4974_, v___y_4975_, v___y_4976_);
                    if leanh::lean_obj_tag(v___x_5047_) == 0 {
                        v_a_5048_ = leanh::lean_ctor_get(v___x_5047_, 0);
                        leanh::lean_inc(v_a_5048_);
                        leanh::lean_dec_ref_known(v___x_5047_, 1);
                        leanh::lean_inc_ref(v_body_5045_);
                        leanh::lean_inc_ref(v_post_4973_);
                        leanh::lean_inc_ref(v_pre_4971_);
                        v___x_5049_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_body_5045_, v___y_4974_, v___y_4975_, v___y_4976_);
                        if leanh::lean_obj_tag(v___x_5049_) == 0 {
                            v_a_5050_ = leanh::lean_ctor_get(v___x_5049_, 0);
                            leanh::lean_inc(v_a_5050_);
                            leanh::lean_dec_ref_known(v___x_5049_, 1);
                            v___x_5051_ = lean_ptr_addr(v_binderType_5044_);
                            v___x_5052_ = lean_ptr_addr(v_a_5048_);
                            v___x_5053_ = lean_usize_dec_eq(v___x_5051_, v___x_5052_);
                            if v___x_5053_ == 0 {
                                v___y_4996_ = v___y_5028_;
                                v___y_4997_ = v_binderInfo_5046_;
                                v___y_4998_ = v_binderName_5043_;
                                v___y_4999_ = v_a_5050_;
                                v___y_5000_ = v_a_5048_;
                                v___y_5001_ = v___x_5053_;
                                state = 2;
                                continue;
                            } else {
                                v___x_5054_ = lean_ptr_addr(v_body_5045_);
                                v___x_5055_ = lean_ptr_addr(v_a_5050_);
                                v___x_5056_ = lean_usize_dec_eq(v___x_5054_, v___x_5055_);
                                v___y_4996_ = v___y_5028_;
                                v___y_4997_ = v_binderInfo_5046_;
                                v___y_4998_ = v_binderName_5043_;
                                v___y_4999_ = v_a_5050_;
                                v___y_5000_ = v_a_5048_;
                                v___y_5001_ = v___x_5056_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5048_);
                            leanh::lean_dec(v_binderName_5043_);
                            leanh::lean_dec_ref_known(v___y_5028_, 3);
                            leanh::lean_dec_ref(v_post_4973_);
                            leanh::lean_dec_ref(v_pre_4971_);
                            return v___x_5049_;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_5043_);
                        leanh::lean_dec_ref_known(v___y_5028_, 3);
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        return v___x_5047_;
                    }
                }
                8 => {
                    v_declName_5057_ = leanh::lean_ctor_get(v___y_5028_, 0);
                    leanh::lean_inc(v_declName_5057_);
                    v_type_5058_ = leanh::lean_ctor_get(v___y_5028_, 1);
                    v_value_5059_ = leanh::lean_ctor_get(v___y_5028_, 2);
                    v_body_5060_ = leanh::lean_ctor_get(v___y_5028_, 3);
                    leanh::lean_inc_ref(v_body_5060_);
                    v_nondep_5061_ = leanh::lean_ctor_get_uint8(
                        v___y_5028_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_5058_);
                    leanh::lean_inc_ref(v_post_4973_);
                    leanh::lean_inc_ref(v_pre_4971_);
                    v___x_5062_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_type_5058_, v___y_4974_, v___y_4975_, v___y_4976_);
                    if leanh::lean_obj_tag(v___x_5062_) == 0 {
                        v_a_5063_ = leanh::lean_ctor_get(v___x_5062_, 0);
                        leanh::lean_inc(v_a_5063_);
                        leanh::lean_dec_ref_known(v___x_5062_, 1);
                        leanh::lean_inc_ref(v_value_5059_);
                        leanh::lean_inc_ref(v_post_4973_);
                        leanh::lean_inc_ref(v_pre_4971_);
                        v___x_5064_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_value_5059_, v___y_4974_, v___y_4975_, v___y_4976_);
                        if leanh::lean_obj_tag(v___x_5064_) == 0 {
                            v_a_5065_ = leanh::lean_ctor_get(v___x_5064_, 0);
                            leanh::lean_inc(v_a_5065_);
                            leanh::lean_dec_ref_known(v___x_5064_, 1);
                            leanh::lean_inc_ref(v_body_5060_);
                            leanh::lean_inc_ref(v_post_4973_);
                            leanh::lean_inc_ref(v_pre_4971_);
                            v___x_5066_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_body_5060_, v___y_4974_, v___y_4975_, v___y_4976_);
                            if leanh::lean_obj_tag(v___x_5066_) == 0 {
                                v_a_5067_ = leanh::lean_ctor_get(v___x_5066_, 0);
                                leanh::lean_inc(v_a_5067_);
                                leanh::lean_dec_ref_known(v___x_5066_, 1);
                                v___x_5068_ = lean_ptr_addr(v_type_5058_);
                                v___x_5069_ = lean_ptr_addr(v_a_5063_);
                                v___x_5070_ = lean_usize_dec_eq(v___x_5068_, v___x_5069_);
                                if v___x_5070_ == 0 {
                                    v___y_4979_ = v_a_5065_;
                                    v___y_4980_ = v_declName_5057_;
                                    v___y_4981_ = v_nondep_5061_;
                                    v___y_4982_ = v_a_5067_;
                                    v___y_4983_ = v___y_5028_;
                                    v___y_4984_ = v_a_5063_;
                                    v___y_4985_ = v_body_5060_;
                                    v___y_4986_ = v___x_5070_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_5071_ = lean_ptr_addr(v_value_5059_);
                                    v___x_5072_ = lean_ptr_addr(v_a_5065_);
                                    v___x_5073_ = lean_usize_dec_eq(v___x_5071_, v___x_5072_);
                                    v___y_4979_ = v_a_5065_;
                                    v___y_4980_ = v_declName_5057_;
                                    v___y_4981_ = v_nondep_5061_;
                                    v___y_4982_ = v_a_5067_;
                                    v___y_4983_ = v___y_5028_;
                                    v___y_4984_ = v_a_5063_;
                                    v___y_4985_ = v_body_5060_;
                                    v___y_4986_ = v___x_5073_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5065_);
                                leanh::lean_dec(v_a_5063_);
                                leanh::lean_dec_ref(v_body_5060_);
                                leanh::lean_dec(v_declName_5057_);
                                leanh::lean_dec_ref_known(v___y_5028_, 4);
                                leanh::lean_dec_ref(v_post_4973_);
                                leanh::lean_dec_ref(v_pre_4971_);
                                return v___x_5066_;
                            }
                        } else {
                            leanh::lean_dec(v_a_5063_);
                            leanh::lean_dec_ref(v_body_5060_);
                            leanh::lean_dec(v_declName_5057_);
                            leanh::lean_dec_ref_known(v___y_5028_, 4);
                            leanh::lean_dec_ref(v_post_4973_);
                            leanh::lean_dec_ref(v_pre_4971_);
                            return v___x_5064_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_5060_);
                        leanh::lean_dec(v_declName_5057_);
                        leanh::lean_dec_ref_known(v___y_5028_, 4);
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        return v___x_5062_;
                    }
                }
                5 => {
                    v_dummy_5074_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1,
                    );
                    v_nargs_5075_ = l_Lean_Expr_getAppNumArgs(v___y_5028_);
                    leanh::lean_inc(v_nargs_5075_);
                    v___x_5076_ = lean_mk_array(v_nargs_5075_, v_dummy_5074_);
                    v___x_5077_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5078_ = lean_nat_sub(v_nargs_5075_, v___x_5077_);
                    leanh::lean_dec(v_nargs_5075_);
                    v___x_5079_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__7(v_pre_4971_, v_post_4973_, v___y_5028_, v___x_5076_, v___x_5078_, v___y_4974_, v___y_4975_, v___y_4976_);
                    return v___x_5079_;
                }
                10 => {
                    v_data_5080_ = leanh::lean_ctor_get(v___y_5028_, 0);
                    v_expr_5081_ = leanh::lean_ctor_get(v___y_5028_, 1);
                    leanh::lean_inc_ref(v_expr_5081_);
                    leanh::lean_inc_ref(v_post_4973_);
                    leanh::lean_inc_ref(v_pre_4971_);
                    v___x_5082_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_expr_5081_, v___y_4974_, v___y_4975_, v___y_4976_);
                    if leanh::lean_obj_tag(v___x_5082_) == 0 {
                        v_a_5083_ = leanh::lean_ctor_get(v___x_5082_, 0);
                        leanh::lean_inc(v_a_5083_);
                        leanh::lean_dec_ref_known(v___x_5082_, 1);
                        v___x_5084_ = lean_ptr_addr(v_expr_5081_);
                        v___x_5085_ = lean_ptr_addr(v_a_5083_);
                        v___x_5086_ = lean_usize_dec_eq(v___x_5084_, v___x_5085_);
                        if v___x_5086_ == 0 {
                            leanh::lean_inc(v_data_5080_);
                            leanh::lean_dec_ref_known(v___y_5028_, 2);
                            v___x_5087_ = l_Lean_Expr_mdata___override(v_data_5080_, v_a_5083_);
                            v___x_5088_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_5087_, v___y_4974_, v___y_4975_, v___y_4976_);
                            return v___x_5088_;
                        } else {
                            leanh::lean_dec(v_a_5083_);
                            v___x_5089_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___y_5028_, v___y_4974_, v___y_4975_, v___y_4976_);
                            return v___x_5089_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_5028_, 2);
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        return v___x_5082_;
                    }
                }
                11 => {
                    v_typeName_5090_ = leanh::lean_ctor_get(v___y_5028_, 0);
                    v_idx_5091_ = leanh::lean_ctor_get(v___y_5028_, 1);
                    v_struct_5092_ = leanh::lean_ctor_get(v___y_5028_, 2);
                    leanh::lean_inc_ref(v_struct_5092_);
                    leanh::lean_inc_ref(v_post_4973_);
                    leanh::lean_inc_ref(v_pre_4971_);
                    v___x_5093_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_4971_, v_post_4973_, v_struct_5092_, v___y_4974_, v___y_4975_, v___y_4976_);
                    if leanh::lean_obj_tag(v___x_5093_) == 0 {
                        v_a_5094_ = leanh::lean_ctor_get(v___x_5093_, 0);
                        leanh::lean_inc(v_a_5094_);
                        leanh::lean_dec_ref_known(v___x_5093_, 1);
                        v___x_5095_ = lean_ptr_addr(v_struct_5092_);
                        v___x_5096_ = lean_ptr_addr(v_a_5094_);
                        v___x_5097_ = lean_usize_dec_eq(v___x_5095_, v___x_5096_);
                        if v___x_5097_ == 0 {
                            leanh::lean_inc(v_idx_5091_);
                            leanh::lean_inc(v_typeName_5090_);
                            leanh::lean_dec_ref_known(v___y_5028_, 3);
                            v___x_5098_ = l_Lean_Expr_proj___override(
                                v_typeName_5090_,
                                v_idx_5091_,
                                v_a_5094_,
                            );
                            v___x_5099_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___x_5098_, v___y_4974_, v___y_4975_, v___y_4976_);
                            return v___x_5099_;
                        } else {
                            leanh::lean_dec(v_a_5094_);
                            v___x_5100_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___y_5028_, v___y_4974_, v___y_4975_, v___y_4976_);
                            return v___x_5100_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_5028_, 3);
                        leanh::lean_dec_ref(v_post_4973_);
                        leanh::lean_dec_ref(v_pre_4971_);
                        return v___x_5093_;
                    }
                }
                _ => {
                    v___x_5101_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_4971_, v_post_4973_, v___y_5028_, v___y_4974_, v___y_4975_, v___y_4976_);
                    return v___x_5101_;
                }
            },
            6 => {
                return v___x_5104_;
            }
            7 => {
                if v_isShared_5116_ == 0 {
                    v___x_5118_ = v___x_5115_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
                    v___x_5118_ = v_reuseFailAlloc_5119_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5118_;
            }
            9 => {
                if v_isShared_5124_ == 0 {
                    v___x_5126_ = v___x_5123_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
                    v___x_5126_ = v_reuseFailAlloc_5127_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__1___boxed(
    mut v___x_5129_: *mut leanh::LeanObject,
    mut v_pre_5130_: *mut leanh::LeanObject,
    mut v_e_5131_: *mut leanh::LeanObject,
    mut v_post_5132_: *mut leanh::LeanObject,
    mut v___y_5133_: *mut leanh::LeanObject,
    mut v___y_5134_: *mut leanh::LeanObject,
    mut v___y_5135_: *mut leanh::LeanObject,
    mut v___y_5136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5137_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__1(v___x_5129_, v_pre_5130_, v_e_5131_, v_post_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
    leanh::lean_dec(v___y_5135_);
    leanh::lean_dec_ref(v___y_5134_);
    leanh::lean_dec(v___y_5133_);
    return v_res_5137_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(
    mut v_pre_5138_: *mut leanh::LeanObject,
    mut v_post_5139_: *mut leanh::LeanObject,
    mut v_e_5140_: *mut leanh::LeanObject,
    mut v_a_5141_: *mut leanh::LeanObject,
    mut v___y_5142_: *mut leanh::LeanObject,
    mut v___y_5143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5164_: u8 = 0;
    let mut v_unused_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v_val_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v_a_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5182_: u8 = 0;
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_5141_);
                v___x_5145_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_5145_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_5145_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_5145_, 2, v_a_5141_);
                v___x_5146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__0(leanh::lean_box(0), v___x_5145_, v___y_5142_, v___y_5143_);
                if leanh::lean_obj_tag(v___x_5146_) == 0 {
                    v_a_5147_ = leanh::lean_ctor_get(v___x_5146_, 0);
                    v_isSharedCheck_5178_ = (!leanh::lean_is_exclusive(v___x_5146_)) as u8;
                    if v_isSharedCheck_5178_ == 0 {
                        v___x_5149_ = v___x_5146_;
                        v_isShared_5150_ = v_isSharedCheck_5178_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5147_);
                        leanh::lean_dec(v___x_5146_);
                        v___x_5149_ = leanh::lean_box(0);
                        v_isShared_5150_ = v_isSharedCheck_5178_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5140_);
                    leanh::lean_dec_ref(v_post_5139_);
                    leanh::lean_dec_ref(v_pre_5138_);
                    v_a_5179_ = leanh::lean_ctor_get(v___x_5146_, 0);
                    v_isSharedCheck_5186_ = (!leanh::lean_is_exclusive(v___x_5146_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5181_ = v___x_5146_;
                        v_isShared_5182_ = v_isSharedCheck_5186_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5179_);
                        leanh::lean_dec(v___x_5146_);
                        v___x_5181_ = leanh::lean_box(0);
                        v_isShared_5182_ = v_isSharedCheck_5186_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___redArg(v_a_5147_, v_e_5140_);
                leanh::lean_dec(v_a_5147_);
                if leanh::lean_obj_tag(v___x_5151_) == 0 {
                    leanh::lean_del_object(v___x_5149_);
                    v___x_5152_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___closed__0;
                    leanh::lean_inc_ref(v_e_5140_);
                    v___f_5153_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    leanh::lean_closure_set(v___f_5153_, 0, v___x_5152_);
                    leanh::lean_closure_set(v___f_5153_, 1, v_pre_5138_);
                    leanh::lean_closure_set(v___f_5153_, 2, v_e_5140_);
                    leanh::lean_closure_set(v___f_5153_, 3, v_post_5139_);
                    v___x_5154_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8___redArg(v___f_5153_, v_a_5141_, v___y_5142_, v___y_5143_);
                    if leanh::lean_obj_tag(v___x_5154_) == 0 {
                        v_a_5155_ = leanh::lean_ctor_get(v___x_5154_, 0);
                        leanh::lean_inc_n(v_a_5155_, 2);
                        leanh::lean_dec_ref_known(v___x_5154_, 1);
                        leanh::lean_inc(v_a_5141_);
                        v___f_5156_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_5156_, 0, v_a_5141_);
                        leanh::lean_closure_set(v___f_5156_, 1, v_e_5140_);
                        leanh::lean_closure_set(v___f_5156_, 2, v_a_5155_);
                        v___x_5157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__0(leanh::lean_box(0), v___f_5156_, v___y_5142_, v___y_5143_);
                        if leanh::lean_obj_tag(v___x_5157_) == 0 {
                            v_isSharedCheck_5164_ =
                                (!leanh::lean_is_exclusive(v___x_5157_)) as u8;
                            if v_isSharedCheck_5164_ == 0 {
                                v_unused_5165_ = leanh::lean_ctor_get(v___x_5157_, 0);
                                leanh::lean_dec(v_unused_5165_);
                                v___x_5159_ = v___x_5157_;
                                v_isShared_5160_ = v_isSharedCheck_5164_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5157_);
                                v___x_5159_ = leanh::lean_box(0);
                                v_isShared_5160_ = v_isSharedCheck_5164_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5155_);
                            v_a_5166_ = leanh::lean_ctor_get(v___x_5157_, 0);
                            v_isSharedCheck_5173_ =
                                (!leanh::lean_is_exclusive(v___x_5157_)) as u8;
                            if v_isSharedCheck_5173_ == 0 {
                                v___x_5168_ = v___x_5157_;
                                v_isShared_5169_ = v_isSharedCheck_5173_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5166_);
                                leanh::lean_dec(v___x_5157_);
                                v___x_5168_ = leanh::lean_box(0);
                                v_isShared_5169_ = v_isSharedCheck_5173_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5140_);
                        return v___x_5154_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5140_);
                    leanh::lean_dec_ref(v_post_5139_);
                    leanh::lean_dec_ref(v_pre_5138_);
                    v_val_5174_ = leanh::lean_ctor_get(v___x_5151_, 0);
                    leanh::lean_inc(v_val_5174_);
                    leanh::lean_dec_ref_known(v___x_5151_, 1);
                    if v_isShared_5150_ == 0 {
                        leanh::lean_ctor_set(v___x_5149_, 0, v_val_5174_);
                        v___x_5176_ = v___x_5149_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5177_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_val_5174_);
                        v___x_5176_ = v_reuseFailAlloc_5177_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5160_ == 0 {
                    leanh::lean_ctor_set(v___x_5159_, 0, v_a_5155_);
                    v___x_5162_ = v___x_5159_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5155_);
                    v___x_5162_ = v_reuseFailAlloc_5163_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5162_;
            }
            4 => {
                if v_isShared_5169_ == 0 {
                    v___x_5171_ = v___x_5168_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
                    v___x_5171_ = v_reuseFailAlloc_5172_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5171_;
            }
            6 => {
                return v___x_5176_;
            }
            7 => {
                if v_isShared_5182_ == 0 {
                    v___x_5184_ = v___x_5181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
                    v___x_5184_ = v_reuseFailAlloc_5185_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(
    mut v_pre_5187_: *mut leanh::LeanObject,
    mut v_post_5188_: *mut leanh::LeanObject,
    mut v_e_5189_: *mut leanh::LeanObject,
    mut v_a_5190_: *mut leanh::LeanObject,
    mut v___y_5191_: *mut leanh::LeanObject,
    mut v___y_5192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v_e_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5213_: u8 = 0;
    let mut v_a_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5217_: u8 = 0;
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_5188_);
                leanh::lean_inc(v___y_5192_);
                leanh::lean_inc_ref(v___y_5191_);
                leanh::lean_inc_ref(v_e_5189_);
                v___x_5194_ = leanh::lean_apply_4(
                    v_post_5188_,
                    v_e_5189_,
                    v___y_5191_,
                    v___y_5192_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5194_) == 0 {
                    v_a_5195_ = leanh::lean_ctor_get(v___x_5194_, 0);
                    v_isSharedCheck_5213_ = (!leanh::lean_is_exclusive(v___x_5194_)) as u8;
                    if v_isSharedCheck_5213_ == 0 {
                        v___x_5197_ = v___x_5194_;
                        v_isShared_5198_ = v_isSharedCheck_5213_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5195_);
                        leanh::lean_dec(v___x_5194_);
                        v___x_5197_ = leanh::lean_box(0);
                        v_isShared_5198_ = v_isSharedCheck_5213_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5189_);
                    leanh::lean_dec_ref(v_post_5188_);
                    leanh::lean_dec_ref(v_pre_5187_);
                    v_a_5214_ = leanh::lean_ctor_get(v___x_5194_, 0);
                    v_isSharedCheck_5221_ = (!leanh::lean_is_exclusive(v___x_5194_)) as u8;
                    if v_isSharedCheck_5221_ == 0 {
                        v___x_5216_ = v___x_5194_;
                        v_isShared_5217_ = v_isSharedCheck_5221_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5214_);
                        leanh::lean_dec(v___x_5194_);
                        v___x_5216_ = leanh::lean_box(0);
                        v_isShared_5217_ = v_isSharedCheck_5221_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_5195_) {
                0 => {
                    leanh::lean_dec_ref(v_e_5189_);
                    leanh::lean_dec_ref(v_post_5188_);
                    leanh::lean_dec_ref(v_pre_5187_);
                    v_e_5199_ = leanh::lean_ctor_get(v_a_5195_, 0);
                    leanh::lean_inc_ref(v_e_5199_);
                    leanh::lean_dec_ref_known(v_a_5195_, 1);
                    if v_isShared_5198_ == 0 {
                        leanh::lean_ctor_set(v___x_5197_, 0, v_e_5199_);
                        v___x_5201_ = v___x_5197_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5202_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_e_5199_);
                        v___x_5201_ = v_reuseFailAlloc_5202_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_5197_);
                    leanh::lean_dec_ref(v_e_5189_);
                    v_e_5203_ = leanh::lean_ctor_get(v_a_5195_, 0);
                    leanh::lean_inc_ref(v_e_5203_);
                    leanh::lean_dec_ref_known(v_a_5195_, 1);
                    v___x_5204_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_5187_, v_post_5188_, v_e_5203_, v_a_5190_, v___y_5191_, v___y_5192_);
                    return v___x_5204_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_5188_);
                    leanh::lean_dec_ref(v_pre_5187_);
                    v_e_x3f_5205_ = leanh::lean_ctor_get(v_a_5195_, 0);
                    leanh::lean_inc(v_e_x3f_5205_);
                    leanh::lean_dec_ref_known(v_a_5195_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_5205_) == 0 {
                        if v_isShared_5198_ == 0 {
                            leanh::lean_ctor_set(v___x_5197_, 0, v_e_5189_);
                            v___x_5207_ = v___x_5197_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5208_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_e_5189_);
                            v___x_5207_ = v_reuseFailAlloc_5208_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5189_);
                        v_val_5209_ = leanh::lean_ctor_get(v_e_x3f_5205_, 0);
                        leanh::lean_inc(v_val_5209_);
                        leanh::lean_dec_ref_known(v_e_x3f_5205_, 1);
                        if v_isShared_5198_ == 0 {
                            leanh::lean_ctor_set(v___x_5197_, 0, v_val_5209_);
                            v___x_5211_ = v___x_5197_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5212_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_val_5209_);
                            v___x_5211_ = v_reuseFailAlloc_5212_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_5201_;
            }
            3 => {
                return v___x_5207_;
            }
            4 => {
                return v___x_5211_;
            }
            5 => {
                if v_isShared_5217_ == 0 {
                    v___x_5219_ = v___x_5216_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5220_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_a_5214_);
                    v___x_5219_ = v_reuseFailAlloc_5220_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5___boxed(
    mut v_pre_5222_: *mut leanh::LeanObject,
    mut v_post_5223_: *mut leanh::LeanObject,
    mut v_e_5224_: *mut leanh::LeanObject,
    mut v_a_5225_: *mut leanh::LeanObject,
    mut v___y_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5229_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__5(v_pre_5222_, v_post_5223_, v_e_5224_, v_a_5225_, v___y_5226_, v___y_5227_);
    leanh::lean_dec(v___y_5227_);
    leanh::lean_dec_ref(v___y_5226_);
    leanh::lean_dec(v_a_5225_);
    return v_res_5229_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__4___boxed(
    mut v_pre_5230_: *mut leanh::LeanObject,
    mut v_post_5231_: *mut leanh::LeanObject,
    mut v_sz_5232_: *mut leanh::LeanObject,
    mut v_i_5233_: *mut leanh::LeanObject,
    mut v_bs_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5239_: usize = 0;
    let mut v_i_boxed_5240_: usize = 0;
    let mut v_res_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5239_ = leanh::lean_unbox_usize(v_sz_5232_);
    leanh::lean_dec(v_sz_5232_);
    v_i_boxed_5240_ = leanh::lean_unbox_usize(v_i_5233_);
    leanh::lean_dec(v_i_5233_);
    v_res_5241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__4(v_pre_5230_, v_post_5231_, v_sz_boxed_5239_, v_i_boxed_5240_, v_bs_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
    leanh::lean_dec(v___y_5237_);
    leanh::lean_dec_ref(v___y_5236_);
    leanh::lean_dec(v___y_5235_);
    return v_res_5241_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__7___boxed(
    mut v_pre_5242_: *mut leanh::LeanObject,
    mut v_post_5243_: *mut leanh::LeanObject,
    mut v_x_5244_: *mut leanh::LeanObject,
    mut v_x_5245_: *mut leanh::LeanObject,
    mut v_x_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
    mut v___y_5250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5251_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__7(v_pre_5242_, v_post_5243_, v_x_5244_, v_x_5245_, v_x_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
    leanh::lean_dec(v___y_5249_);
    leanh::lean_dec_ref(v___y_5248_);
    leanh::lean_dec(v___y_5247_);
    return v_res_5251_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___boxed(
    mut v_pre_5252_: *mut leanh::LeanObject,
    mut v_post_5253_: *mut leanh::LeanObject,
    mut v_e_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v___y_5256_: *mut leanh::LeanObject,
    mut v___y_5257_: *mut leanh::LeanObject,
    mut v___y_5258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5259_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_5252_, v_post_5253_, v_e_5254_, v_a_5255_, v___y_5256_, v___y_5257_);
    leanh::lean_dec(v___y_5257_);
    leanh::lean_dec_ref(v___y_5256_);
    leanh::lean_dec(v_a_5255_);
    return v_res_5259_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___lam__0(
    mut v_00_u03b1_5260_: *mut leanh::LeanObject,
    mut v_x_5261_: *mut leanh::LeanObject,
    mut v___y_5262_: *mut leanh::LeanObject,
    mut v___y_5263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5265_ = leanh::lean_apply_1(v_x_5261_, leanh::lean_box(0));
    v___x_5266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5266_, 0, v___x_5265_);
    return v___x_5266_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___lam__0___boxed(
    mut v_00_u03b1_5267_: *mut leanh::LeanObject,
    mut v_x_5268_: *mut leanh::LeanObject,
    mut v___y_5269_: *mut leanh::LeanObject,
    mut v___y_5270_: *mut leanh::LeanObject,
    mut v___y_5271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5272_ = l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___lam__0(
        v_00_u03b1_5267_,
        v_x_5268_,
        v___y_5269_,
        v___y_5270_,
    );
    leanh::lean_dec(v___y_5270_);
    leanh::lean_dec_ref(v___y_5269_);
    return v_res_5272_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5273_ = leanh::lean_box(0);
    v___x_5274_ = leanh::lean_unsigned_to_nat(16);
    v___x_5275_ = lean_mk_array(v___x_5274_, v___x_5273_);
    return v___x_5275_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5276_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__0_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__0,
    );
    v___x_5277_ = leanh::lean_unsigned_to_nat(0);
    v___x_5278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5278_, 0, v___x_5277_);
    leanh::lean_ctor_set(v___x_5278_, 1, v___x_5276_);
    return v___x_5278_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5279_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__1_once
        ),
        _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__1,
    );
    v___x_5280_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_5280_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5280_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5280_, 2, v___x_5279_);
    return v___x_5280_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1(
    mut v_input_5281_: *mut leanh::LeanObject,
    mut v_pre_5282_: *mut leanh::LeanObject,
    mut v_post_5283_: *mut leanh::LeanObject,
    mut v___y_5284_: *mut leanh::LeanObject,
    mut v___y_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5296_: u8 = 0;
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut v_unused_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2);
                v___x_5288_ =
                    l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___lam__0(
                        leanh::lean_box(0),
                        v___x_5287_,
                        v___y_5284_,
                        v___y_5285_,
                    );
                v_a_5289_ = leanh::lean_ctor_get(v___x_5288_, 0);
                leanh::lean_inc(v_a_5289_);
                leanh::lean_dec_ref(v___x_5288_);
                v___x_5290_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2(v_pre_5282_, v_post_5283_, v_input_5281_, v_a_5289_, v___y_5284_, v___y_5285_);
                if leanh::lean_obj_tag(v___x_5290_) == 0 {
                    v_a_5291_ = leanh::lean_ctor_get(v___x_5290_, 0);
                    leanh::lean_inc(v_a_5291_);
                    leanh::lean_dec_ref_known(v___x_5290_, 1);
                    v___x_5292_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_5292_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_5292_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_5292_, 2, v_a_5289_);
                    v___x_5293_ = l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___lam__0(leanh::lean_box(0), v___x_5292_, v___y_5284_, v___y_5285_);
                    v_isSharedCheck_5300_ = (!leanh::lean_is_exclusive(v___x_5293_)) as u8;
                    if v_isSharedCheck_5300_ == 0 {
                        v_unused_5301_ = leanh::lean_ctor_get(v___x_5293_, 0);
                        leanh::lean_dec(v_unused_5301_);
                        v___x_5295_ = v___x_5293_;
                        v_isShared_5296_ = v_isSharedCheck_5300_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5293_);
                        v___x_5295_ = leanh::lean_box(0);
                        v_isShared_5296_ = v_isSharedCheck_5300_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5289_);
                    return v___x_5290_;
                }
            }
            1 => {
                if v_isShared_5296_ == 0 {
                    leanh::lean_ctor_set(v___x_5295_, 0, v_a_5291_);
                    v___x_5298_ = v___x_5295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5291_);
                    v___x_5298_ = v_reuseFailAlloc_5299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___boxed(
    mut v_input_5302_: *mut leanh::LeanObject,
    mut v_pre_5303_: *mut leanh::LeanObject,
    mut v_post_5304_: *mut leanh::LeanObject,
    mut v___y_5305_: *mut leanh::LeanObject,
    mut v___y_5306_: *mut leanh::LeanObject,
    mut v___y_5307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5308_ = l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1(
        v_input_5302_,
        v_pre_5303_,
        v_post_5304_,
        v___y_5305_,
        v___y_5306_,
    );
    leanh::lean_dec(v___y_5306_);
    leanh::lean_dec_ref(v___y_5305_);
    return v_res_5308_;
}
pub unsafe fn l_Lean_Compiler_LCNF_macroInline(
    mut v_e_5311_: *mut leanh::LeanObject,
    mut v_a_5312_: *mut leanh::LeanObject,
    mut v_a_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5315_ = l_Lean_Compiler_LCNF_macroInline___closed__0;
    v___f_5316_ = l_Lean_Compiler_LCNF_macroInline___closed__1;
    v___x_5317_ = l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1(
        v_e_5311_,
        v___f_5316_,
        v___f_5315_,
        v_a_5312_,
        v_a_5313_,
    );
    return v___x_5317_;
}
pub unsafe fn l_Lean_Compiler_LCNF_macroInline___boxed(
    mut v_e_5318_: *mut leanh::LeanObject,
    mut v_a_5319_: *mut leanh::LeanObject,
    mut v_a_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5322_ = l_Lean_Compiler_LCNF_macroInline(v_e_5318_, v_a_5319_, v_a_5320_);
    leanh::lean_dec(v_a_5320_);
    leanh::lean_dec_ref(v_a_5319_);
    return v_res_5322_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0(
    mut v_00_u03b1_5323_: *mut leanh::LeanObject,
    mut v_constName_5324_: *mut leanh::LeanObject,
    mut v___y_5325_: *mut leanh::LeanObject,
    mut v___y_5326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5328_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0___redArg(v_constName_5324_, v___y_5325_, v___y_5326_);
    return v___x_5328_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0___boxed(
    mut v_00_u03b1_5329_: *mut leanh::LeanObject,
    mut v_constName_5330_: *mut leanh::LeanObject,
    mut v___y_5331_: *mut leanh::LeanObject,
    mut v___y_5332_: *mut leanh::LeanObject,
    mut v___y_5333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0(v_00_u03b1_5329_, v_constName_5330_, v___y_5331_, v___y_5332_);
    leanh::lean_dec(v___y_5332_);
    leanh::lean_dec_ref(v___y_5331_);
    return v_res_5334_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5335_: *mut leanh::LeanObject,
    mut v_ref_5336_: *mut leanh::LeanObject,
    mut v_constName_5337_: *mut leanh::LeanObject,
    mut v___y_5338_: *mut leanh::LeanObject,
    mut v___y_5339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5341_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg(v_ref_5336_, v_constName_5337_, v___y_5338_, v___y_5339_);
    return v___x_5341_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5342_: *mut leanh::LeanObject,
    mut v_ref_5343_: *mut leanh::LeanObject,
    mut v_constName_5344_: *mut leanh::LeanObject,
    mut v___y_5345_: *mut leanh::LeanObject,
    mut v___y_5346_: *mut leanh::LeanObject,
    mut v___y_5347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5348_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1(v_00_u03b1_5342_, v_ref_5343_, v_constName_5344_, v___y_5345_, v___y_5346_);
    leanh::lean_dec(v___y_5346_);
    leanh::lean_dec_ref(v___y_5345_);
    leanh::lean_dec(v_ref_5343_);
    return v_res_5348_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6(
    mut v_00_u03b2_5349_: *mut leanh::LeanObject,
    mut v_m_5350_: *mut leanh::LeanObject,
    mut v_a_5351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___redArg(v_m_5350_, v_a_5351_);
    return v___x_5352_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_5353_: *mut leanh::LeanObject,
    mut v_m_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6(v_00_u03b2_5353_, v_m_5354_, v_a_5355_);
    leanh::lean_dec_ref(v_a_5355_);
    leanh::lean_dec_ref(v_m_5354_);
    return v_res_5356_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11(
    mut v_00_u03b1_5357_: *mut leanh::LeanObject,
    mut v_ref_5358_: *mut leanh::LeanObject,
    mut v___y_5359_: *mut leanh::LeanObject,
    mut v___y_5360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5362_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg(v_ref_5358_);
    return v___x_5362_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___boxed(
    mut v_00_u03b1_5363_: *mut leanh::LeanObject,
    mut v_ref_5364_: *mut leanh::LeanObject,
    mut v___y_5365_: *mut leanh::LeanObject,
    mut v___y_5366_: *mut leanh::LeanObject,
    mut v___y_5367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5368_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11(v_00_u03b1_5363_, v_ref_5364_, v___y_5365_, v___y_5366_);
    leanh::lean_dec(v___y_5366_);
    leanh::lean_dec_ref(v___y_5365_);
    return v_res_5368_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12(
    mut v_00_u03b1_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5373_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___redArg();
    return v___x_5373_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12___boxed(
    mut v_00_u03b1_5374_: *mut leanh::LeanObject,
    mut v___y_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5378_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__12(v_00_u03b1_5374_, v___y_5375_, v___y_5376_);
    leanh::lean_dec(v___y_5376_);
    leanh::lean_dec_ref(v___y_5375_);
    return v_res_5378_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8(
    mut v_00_u03b1_5379_: *mut leanh::LeanObject,
    mut v_x_5380_: *mut leanh::LeanObject,
    mut v___y_5381_: *mut leanh::LeanObject,
    mut v___y_5382_: *mut leanh::LeanObject,
    mut v___y_5383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8___redArg(v_x_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
    return v___x_5385_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8___boxed(
    mut v_00_u03b1_5386_: *mut leanh::LeanObject,
    mut v_x_5387_: *mut leanh::LeanObject,
    mut v___y_5388_: *mut leanh::LeanObject,
    mut v___y_5389_: *mut leanh::LeanObject,
    mut v___y_5390_: *mut leanh::LeanObject,
    mut v___y_5391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5392_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8(v_00_u03b1_5386_, v_x_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
    leanh::lean_dec(v___y_5390_);
    leanh::lean_dec_ref(v___y_5389_);
    leanh::lean_dec(v___y_5388_);
    return v_res_5392_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9(
    mut v_00_u03b2_5393_: *mut leanh::LeanObject,
    mut v_m_5394_: *mut leanh::LeanObject,
    mut v_a_5395_: *mut leanh::LeanObject,
    mut v_b_5396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5397_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9___redArg(v_m_5394_, v_a_5395_, v_b_5396_);
    return v___x_5397_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_5398_: *mut leanh::LeanObject,
    mut v_ref_5399_: *mut leanh::LeanObject,
    mut v_msg_5400_: *mut leanh::LeanObject,
    mut v_declHint_5401_: *mut leanh::LeanObject,
    mut v___y_5402_: *mut leanh::LeanObject,
    mut v___y_5403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_5399_, v_msg_5400_, v_declHint_5401_, v___y_5402_, v___y_5403_);
    return v___x_5405_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_5406_: *mut leanh::LeanObject,
    mut v_ref_5407_: *mut leanh::LeanObject,
    mut v_msg_5408_: *mut leanh::LeanObject,
    mut v_declHint_5409_: *mut leanh::LeanObject,
    mut v___y_5410_: *mut leanh::LeanObject,
    mut v___y_5411_: *mut leanh::LeanObject,
    mut v___y_5412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5413_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_5406_, v_ref_5407_, v_msg_5408_, v_declHint_5409_, v___y_5410_, v___y_5411_);
    leanh::lean_dec(v___y_5411_);
    leanh::lean_dec_ref(v___y_5410_);
    leanh::lean_dec(v_ref_5407_);
    return v_res_5413_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8(
    mut v_00_u03b2_5414_: *mut leanh::LeanObject,
    mut v_a_5415_: *mut leanh::LeanObject,
    mut v_x_5416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5417_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8___redArg(v_a_5415_, v_x_5416_);
    return v___x_5417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8___boxed(
    mut v_00_u03b2_5418_: *mut leanh::LeanObject,
    mut v_a_5419_: *mut leanh::LeanObject,
    mut v_x_5420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5421_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6_spec__8(v_00_u03b2_5418_, v_a_5419_, v_x_5420_);
    leanh::lean_dec(v_x_5420_);
    leanh::lean_dec_ref(v_a_5419_);
    return v_res_5421_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14(
    mut v_00_u03b2_5422_: *mut leanh::LeanObject,
    mut v_a_5423_: *mut leanh::LeanObject,
    mut v_x_5424_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5425_: u8 = 0;
    v___x_5425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14___redArg(v_a_5423_, v_x_5424_);
    return v___x_5425_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14___boxed(
    mut v_00_u03b2_5426_: *mut leanh::LeanObject,
    mut v_a_5427_: *mut leanh::LeanObject,
    mut v_x_5428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5429_: u8 = 0;
    let mut v_r_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__14(v_00_u03b2_5426_, v_a_5427_, v_x_5428_);
    leanh::lean_dec(v_x_5428_);
    leanh::lean_dec_ref(v_a_5427_);
    v_r_5430_ = leanh::lean_box((v_res_5429_) as usize);
    return v_r_5430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15(
    mut v_00_u03b2_5431_: *mut leanh::LeanObject,
    mut v_data_5432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15___redArg(v_data_5432_);
    return v___x_5433_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__16(
    mut v_00_u03b2_5434_: *mut leanh::LeanObject,
    mut v_a_5435_: *mut leanh::LeanObject,
    mut v_b_5436_: *mut leanh::LeanObject,
    mut v_x_5437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__16___redArg(v_a_5435_, v_b_5436_, v_x_5437_);
    return v___x_5438_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14(
    mut v_msg_5439_: *mut leanh::LeanObject,
    mut v_declHint_5440_: *mut leanh::LeanObject,
    mut v___y_5441_: *mut leanh::LeanObject,
    mut v___y_5442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg(v_msg_5439_, v_declHint_5440_, v___y_5442_);
    return v___x_5444_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___boxed(
    mut v_msg_5445_: *mut leanh::LeanObject,
    mut v_declHint_5446_: *mut leanh::LeanObject,
    mut v___y_5447_: *mut leanh::LeanObject,
    mut v___y_5448_: *mut leanh::LeanObject,
    mut v___y_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14(v_msg_5445_, v_declHint_5446_, v___y_5447_, v___y_5448_);
    leanh::lean_dec(v___y_5448_);
    leanh::lean_dec_ref(v___y_5447_);
    return v_res_5450_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b1_5451_: *mut leanh::LeanObject,
    mut v_ref_5452_: *mut leanh::LeanObject,
    mut v_msg_5453_: *mut leanh::LeanObject,
    mut v___y_5454_: *mut leanh::LeanObject,
    mut v___y_5455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5457_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_5452_, v_msg_5453_, v___y_5454_, v___y_5455_);
    return v___x_5457_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b1_5458_: *mut leanh::LeanObject,
    mut v_ref_5459_: *mut leanh::LeanObject,
    mut v_msg_5460_: *mut leanh::LeanObject,
    mut v___y_5461_: *mut leanh::LeanObject,
    mut v___y_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5464_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03b1_5458_, v_ref_5459_, v_msg_5460_, v___y_5461_, v___y_5462_);
    leanh::lean_dec(v___y_5462_);
    leanh::lean_dec_ref(v___y_5461_);
    leanh::lean_dec(v_ref_5459_);
    return v_res_5464_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18(
    mut v_00_u03b2_5465_: *mut leanh::LeanObject,
    mut v_i_5466_: *mut leanh::LeanObject,
    mut v_source_5467_: *mut leanh::LeanObject,
    mut v_target_5468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5469_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18___redArg(v_i_5466_, v_source_5467_, v_target_5468_);
    return v___x_5469_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16(
    mut v_00_u03b1_5470_: *mut leanh::LeanObject,
    mut v_msg_5471_: *mut leanh::LeanObject,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v___y_5473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5475_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16___redArg(v_msg_5471_, v___y_5472_, v___y_5473_);
    return v___x_5475_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16___boxed(
    mut v_00_u03b1_5476_: *mut leanh::LeanObject,
    mut v_msg_5477_: *mut leanh::LeanObject,
    mut v___y_5478_: *mut leanh::LeanObject,
    mut v___y_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16(v_00_u03b1_5476_, v_msg_5477_, v___y_5478_, v___y_5479_);
    leanh::lean_dec(v___y_5479_);
    leanh::lean_dec_ref(v___y_5478_);
    return v_res_5481_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18_spec__21(
    mut v_00_u03b2_5482_: *mut leanh::LeanObject,
    mut v_x_5483_: *mut leanh::LeanObject,
    mut v_x_5484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5485_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__9_spec__15_spec__18_spec__21___redArg(v_x_5483_, v_x_5484_);
    return v___x_5485_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0(
    mut v_k_5486_: *mut leanh::LeanObject,
    mut v_b_5487_: *mut leanh::LeanObject,
    mut v___y_5488_: *mut leanh::LeanObject,
    mut v___y_5489_: *mut leanh::LeanObject,
    mut v___y_5490_: *mut leanh::LeanObject,
    mut v___y_5491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_5491_);
    leanh::lean_inc_ref(v___y_5490_);
    leanh::lean_inc(v___y_5489_);
    leanh::lean_inc_ref(v___y_5488_);
    v___x_5493_ = leanh::lean_apply_6(
        v_k_5486_,
        v_b_5487_,
        v___y_5488_,
        v___y_5489_,
        v___y_5490_,
        v___y_5491_,
        leanh::lean_box(0),
    );
    return v___x_5493_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0___boxed(
    mut v_k_5494_: *mut leanh::LeanObject,
    mut v_b_5495_: *mut leanh::LeanObject,
    mut v___y_5496_: *mut leanh::LeanObject,
    mut v___y_5497_: *mut leanh::LeanObject,
    mut v___y_5498_: *mut leanh::LeanObject,
    mut v___y_5499_: *mut leanh::LeanObject,
    mut v___y_5500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5501_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0(v_k_5494_, v_b_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
    leanh::lean_dec(v___y_5499_);
    leanh::lean_dec_ref(v___y_5498_);
    leanh::lean_dec(v___y_5497_);
    leanh::lean_dec_ref(v___y_5496_);
    return v_res_5501_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(
    mut v_name_5502_: *mut leanh::LeanObject,
    mut v_type_5503_: *mut leanh::LeanObject,
    mut v_val_5504_: *mut leanh::LeanObject,
    mut v_k_5505_: *mut leanh::LeanObject,
    mut v_nondep_5506_: u8,
    mut v_kind_5507_: u8,
    mut v___y_5508_: *mut leanh::LeanObject,
    mut v___y_5509_: *mut leanh::LeanObject,
    mut v___y_5510_: *mut leanh::LeanObject,
    mut v___y_5511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_a_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5513_ = leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_5513_, 0, v_k_5505_);
                v___x_5514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_5502_,
                    v_type_5503_,
                    v_val_5504_,
                    v___f_5513_,
                    v_nondep_5506_,
                    v_kind_5507_,
                    v___y_5508_,
                    v___y_5509_,
                    v___y_5510_,
                    v___y_5511_,
                );
                if leanh::lean_obj_tag(v___x_5514_) == 0 {
                    v_a_5515_ = leanh::lean_ctor_get(v___x_5514_, 0);
                    v_isSharedCheck_5522_ = (!leanh::lean_is_exclusive(v___x_5514_)) as u8;
                    if v_isSharedCheck_5522_ == 0 {
                        v___x_5517_ = v___x_5514_;
                        v_isShared_5518_ = v_isSharedCheck_5522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5515_);
                        leanh::lean_dec(v___x_5514_);
                        v___x_5517_ = leanh::lean_box(0);
                        v_isShared_5518_ = v_isSharedCheck_5522_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5523_ = leanh::lean_ctor_get(v___x_5514_, 0);
                    v_isSharedCheck_5530_ = (!leanh::lean_is_exclusive(v___x_5514_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v___x_5514_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5523_);
                        leanh::lean_dec(v___x_5514_);
                        v___x_5525_ = leanh::lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5518_ == 0 {
                    v___x_5520_ = v___x_5517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
                    v___x_5520_ = v_reuseFailAlloc_5521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5520_;
            }
            3 => {
                if v_isShared_5526_ == 0 {
                    v___x_5528_ = v___x_5525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___boxed(
    mut v_name_5531_: *mut leanh::LeanObject,
    mut v_type_5532_: *mut leanh::LeanObject,
    mut v_val_5533_: *mut leanh::LeanObject,
    mut v_k_5534_: *mut leanh::LeanObject,
    mut v_nondep_5535_: *mut leanh::LeanObject,
    mut v_kind_5536_: *mut leanh::LeanObject,
    mut v___y_5537_: *mut leanh::LeanObject,
    mut v___y_5538_: *mut leanh::LeanObject,
    mut v___y_5539_: *mut leanh::LeanObject,
    mut v___y_5540_: *mut leanh::LeanObject,
    mut v___y_5541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_5542_: u8 = 0;
    let mut v_kind_boxed_5543_: u8 = 0;
    let mut v_res_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5542_ = (leanh::lean_unbox(v_nondep_5535_) as u8);
    v_kind_boxed_5543_ = (leanh::lean_unbox(v_kind_5536_) as u8);
    v_res_5544_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(v_name_5531_, v_type_5532_, v_val_5533_, v_k_5534_, v_nondep_boxed_5542_, v_kind_boxed_5543_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
    leanh::lean_dec(v___y_5540_);
    leanh::lean_dec_ref(v___y_5539_);
    leanh::lean_dec(v___y_5538_);
    leanh::lean_dec_ref(v___y_5537_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(
    mut v_00_u03b1_5545_: *mut leanh::LeanObject,
    mut v_name_5546_: *mut leanh::LeanObject,
    mut v_type_5547_: *mut leanh::LeanObject,
    mut v_val_5548_: *mut leanh::LeanObject,
    mut v_k_5549_: *mut leanh::LeanObject,
    mut v_nondep_5550_: u8,
    mut v_kind_5551_: u8,
    mut v___y_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
    mut v___y_5554_: *mut leanh::LeanObject,
    mut v___y_5555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5557_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(v_name_5546_, v_type_5547_, v_val_5548_, v_k_5549_, v_nondep_5550_, v_kind_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_);
    return v___x_5557_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___boxed(
    mut v_00_u03b1_5558_: *mut leanh::LeanObject,
    mut v_name_5559_: *mut leanh::LeanObject,
    mut v_type_5560_: *mut leanh::LeanObject,
    mut v_val_5561_: *mut leanh::LeanObject,
    mut v_k_5562_: *mut leanh::LeanObject,
    mut v_nondep_5563_: *mut leanh::LeanObject,
    mut v_kind_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
    mut v___y_5566_: *mut leanh::LeanObject,
    mut v___y_5567_: *mut leanh::LeanObject,
    mut v___y_5568_: *mut leanh::LeanObject,
    mut v___y_5569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_5570_: u8 = 0;
    let mut v_kind_boxed_5571_: u8 = 0;
    let mut v_res_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5570_ = (leanh::lean_unbox(v_nondep_5563_) as u8);
    v_kind_boxed_5571_ = (leanh::lean_unbox(v_kind_5564_) as u8);
    v_res_5572_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(v_00_u03b1_5558_, v_name_5559_, v_type_5560_, v_val_5561_, v_k_5562_, v_nondep_boxed_5570_, v_kind_boxed_5571_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
    leanh::lean_dec(v___y_5568_);
    leanh::lean_dec_ref(v___y_5567_);
    leanh::lean_dec(v___y_5566_);
    leanh::lean_dec_ref(v___y_5565_);
    return v_res_5572_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0(
    mut v_k_5573_: *mut leanh::LeanObject,
    mut v_b_5574_: *mut leanh::LeanObject,
    mut v_c_5575_: *mut leanh::LeanObject,
    mut v___y_5576_: *mut leanh::LeanObject,
    mut v___y_5577_: *mut leanh::LeanObject,
    mut v___y_5578_: *mut leanh::LeanObject,
    mut v___y_5579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_5579_);
    leanh::lean_inc_ref(v___y_5578_);
    leanh::lean_inc(v___y_5577_);
    leanh::lean_inc_ref(v___y_5576_);
    v___x_5581_ = leanh::lean_apply_7(
        v_k_5573_,
        v_b_5574_,
        v_c_5575_,
        v___y_5576_,
        v___y_5577_,
        v___y_5578_,
        v___y_5579_,
        leanh::lean_box(0),
    );
    return v___x_5581_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0___boxed(
    mut v_k_5582_: *mut leanh::LeanObject,
    mut v_b_5583_: *mut leanh::LeanObject,
    mut v_c_5584_: *mut leanh::LeanObject,
    mut v___y_5585_: *mut leanh::LeanObject,
    mut v___y_5586_: *mut leanh::LeanObject,
    mut v___y_5587_: *mut leanh::LeanObject,
    mut v___y_5588_: *mut leanh::LeanObject,
    mut v___y_5589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5590_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0(v_k_5582_, v_b_5583_, v_c_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_);
    leanh::lean_dec(v___y_5588_);
    leanh::lean_dec_ref(v___y_5587_);
    leanh::lean_dec(v___y_5586_);
    leanh::lean_dec_ref(v___y_5585_);
    return v_res_5590_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(
    mut v_type_5591_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5592_: *mut leanh::LeanObject,
    mut v_k_5593_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5594_: u8,
    mut v_whnfType_5595_: u8,
    mut v___y_5596_: *mut leanh::LeanObject,
    mut v___y_5597_: *mut leanh::LeanObject,
    mut v___y_5598_: *mut leanh::LeanObject,
    mut v___y_5599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut v_a_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5601_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_5601_, 0, v_k_5593_);
                v___x_5602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
                    v_type_5591_,
                    v_maxFVars_x3f_5592_,
                    v___f_5601_,
                    v_cleanupAnnotations_5594_,
                    v_whnfType_5595_,
                    v___y_5596_,
                    v___y_5597_,
                    v___y_5598_,
                    v___y_5599_,
                );
                if leanh::lean_obj_tag(v___x_5602_) == 0 {
                    v_a_5603_ = leanh::lean_ctor_get(v___x_5602_, 0);
                    v_isSharedCheck_5610_ = (!leanh::lean_is_exclusive(v___x_5602_)) as u8;
                    if v_isSharedCheck_5610_ == 0 {
                        v___x_5605_ = v___x_5602_;
                        v_isShared_5606_ = v_isSharedCheck_5610_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5603_);
                        leanh::lean_dec(v___x_5602_);
                        v___x_5605_ = leanh::lean_box(0);
                        v_isShared_5606_ = v_isSharedCheck_5610_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5611_ = leanh::lean_ctor_get(v___x_5602_, 0);
                    v_isSharedCheck_5618_ = (!leanh::lean_is_exclusive(v___x_5602_)) as u8;
                    if v_isSharedCheck_5618_ == 0 {
                        v___x_5613_ = v___x_5602_;
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5611_);
                        leanh::lean_dec(v___x_5602_);
                        v___x_5613_ = leanh::lean_box(0);
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5606_ == 0 {
                    v___x_5608_ = v___x_5605_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5608_;
            }
            3 => {
                if v_isShared_5614_ == 0 {
                    v___x_5616_ = v___x_5613_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
                    v___x_5616_ = v_reuseFailAlloc_5617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___boxed(
    mut v_type_5619_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5620_: *mut leanh::LeanObject,
    mut v_k_5621_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5622_: *mut leanh::LeanObject,
    mut v_whnfType_5623_: *mut leanh::LeanObject,
    mut v___y_5624_: *mut leanh::LeanObject,
    mut v___y_5625_: *mut leanh::LeanObject,
    mut v___y_5626_: *mut leanh::LeanObject,
    mut v___y_5627_: *mut leanh::LeanObject,
    mut v___y_5628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5629_: u8 = 0;
    let mut v_whnfType_boxed_5630_: u8 = 0;
    let mut v_res_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5629_ = (leanh::lean_unbox(v_cleanupAnnotations_5622_) as u8);
    v_whnfType_boxed_5630_ = (leanh::lean_unbox(v_whnfType_5623_) as u8);
    v_res_5631_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(v_type_5619_, v_maxFVars_x3f_5620_, v_k_5621_, v_cleanupAnnotations_boxed_5629_, v_whnfType_boxed_5630_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
    leanh::lean_dec(v___y_5627_);
    leanh::lean_dec_ref(v___y_5626_);
    leanh::lean_dec(v___y_5625_);
    leanh::lean_dec_ref(v___y_5624_);
    return v_res_5631_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(
    mut v_00_u03b1_5632_: *mut leanh::LeanObject,
    mut v_type_5633_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5634_: *mut leanh::LeanObject,
    mut v_k_5635_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5636_: u8,
    mut v_whnfType_5637_: u8,
    mut v___y_5638_: *mut leanh::LeanObject,
    mut v___y_5639_: *mut leanh::LeanObject,
    mut v___y_5640_: *mut leanh::LeanObject,
    mut v___y_5641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5643_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(v_type_5633_, v_maxFVars_x3f_5634_, v_k_5635_, v_cleanupAnnotations_5636_, v_whnfType_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
    return v___x_5643_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___boxed(
    mut v_00_u03b1_5644_: *mut leanh::LeanObject,
    mut v_type_5645_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_5646_: *mut leanh::LeanObject,
    mut v_k_5647_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5648_: *mut leanh::LeanObject,
    mut v_whnfType_5649_: *mut leanh::LeanObject,
    mut v___y_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
    mut v___y_5653_: *mut leanh::LeanObject,
    mut v___y_5654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5655_: u8 = 0;
    let mut v_whnfType_boxed_5656_: u8 = 0;
    let mut v_res_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5655_ = (leanh::lean_unbox(v_cleanupAnnotations_5648_) as u8);
    v_whnfType_boxed_5656_ = (leanh::lean_unbox(v_whnfType_5649_) as u8);
    v_res_5657_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(v_00_u03b1_5644_, v_type_5645_, v_maxFVars_x3f_5646_, v_k_5647_, v_cleanupAnnotations_boxed_5655_, v_whnfType_boxed_5656_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_);
    leanh::lean_dec(v___y_5653_);
    leanh::lean_dec_ref(v___y_5652_);
    leanh::lean_dec(v___y_5651_);
    leanh::lean_dec_ref(v___y_5650_);
    return v_res_5657_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___redArg(
    mut v_e_5658_: *mut leanh::LeanObject,
    mut v_k_5659_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5660_: u8,
    mut v___y_5661_: *mut leanh::LeanObject,
    mut v___y_5662_: *mut leanh::LeanObject,
    mut v___y_5663_: *mut leanh::LeanObject,
    mut v___y_5664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5674_: u8 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_a_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5666_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_5666_, 0, v_k_5659_);
                v___x_5667_ = 1;
                v___x_5668_ = 0;
                v___x_5669_ = leanh::lean_box(0);
                v___x_5670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_5658_,
                    v___x_5667_,
                    v___x_5668_,
                    v___x_5667_,
                    v___x_5668_,
                    v___x_5669_,
                    v___f_5666_,
                    v_cleanupAnnotations_5660_,
                    v___y_5661_,
                    v___y_5662_,
                    v___y_5663_,
                    v___y_5664_,
                );
                if leanh::lean_obj_tag(v___x_5670_) == 0 {
                    v_a_5671_ = leanh::lean_ctor_get(v___x_5670_, 0);
                    v_isSharedCheck_5678_ = (!leanh::lean_is_exclusive(v___x_5670_)) as u8;
                    if v_isSharedCheck_5678_ == 0 {
                        v___x_5673_ = v___x_5670_;
                        v_isShared_5674_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5671_);
                        leanh::lean_dec(v___x_5670_);
                        v___x_5673_ = leanh::lean_box(0);
                        v_isShared_5674_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5679_ = leanh::lean_ctor_get(v___x_5670_, 0);
                    v_isSharedCheck_5686_ = (!leanh::lean_is_exclusive(v___x_5670_)) as u8;
                    if v_isSharedCheck_5686_ == 0 {
                        v___x_5681_ = v___x_5670_;
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5679_);
                        leanh::lean_dec(v___x_5670_);
                        v___x_5681_ = leanh::lean_box(0);
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5674_ == 0 {
                    v___x_5676_ = v___x_5673_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
                    v___x_5676_ = v_reuseFailAlloc_5677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5676_;
            }
            3 => {
                if v_isShared_5682_ == 0 {
                    v___x_5684_ = v___x_5681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_a_5679_);
                    v___x_5684_ = v_reuseFailAlloc_5685_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___redArg___boxed(
    mut v_e_5687_: *mut leanh::LeanObject,
    mut v_k_5688_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5689_: *mut leanh::LeanObject,
    mut v___y_5690_: *mut leanh::LeanObject,
    mut v___y_5691_: *mut leanh::LeanObject,
    mut v___y_5692_: *mut leanh::LeanObject,
    mut v___y_5693_: *mut leanh::LeanObject,
    mut v___y_5694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5695_: u8 = 0;
    let mut v_res_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5695_ = (leanh::lean_unbox(v_cleanupAnnotations_5689_) as u8);
    v_res_5696_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___redArg(v_e_5687_, v_k_5688_, v_cleanupAnnotations_boxed_5695_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_);
    leanh::lean_dec(v___y_5693_);
    leanh::lean_dec_ref(v___y_5692_);
    leanh::lean_dec(v___y_5691_);
    leanh::lean_dec_ref(v___y_5690_);
    return v_res_5696_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2(
    mut v_00_u03b1_5697_: *mut leanh::LeanObject,
    mut v_e_5698_: *mut leanh::LeanObject,
    mut v_k_5699_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5700_: u8,
    mut v___y_5701_: *mut leanh::LeanObject,
    mut v___y_5702_: *mut leanh::LeanObject,
    mut v___y_5703_: *mut leanh::LeanObject,
    mut v___y_5704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5706_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___redArg(v_e_5698_, v_k_5699_, v_cleanupAnnotations_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
    return v___x_5706_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___boxed(
    mut v_00_u03b1_5707_: *mut leanh::LeanObject,
    mut v_e_5708_: *mut leanh::LeanObject,
    mut v_k_5709_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_5710_: *mut leanh::LeanObject,
    mut v___y_5711_: *mut leanh::LeanObject,
    mut v___y_5712_: *mut leanh::LeanObject,
    mut v___y_5713_: *mut leanh::LeanObject,
    mut v___y_5714_: *mut leanh::LeanObject,
    mut v___y_5715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5716_: u8 = 0;
    let mut v_res_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5716_ = (leanh::lean_unbox(v_cleanupAnnotations_5710_) as u8);
    v_res_5717_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2(v_00_u03b1_5707_, v_e_5708_, v_k_5709_, v_cleanupAnnotations_boxed_5716_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
    leanh::lean_dec(v___y_5714_);
    leanh::lean_dec_ref(v___y_5713_);
    leanh::lean_dec(v___y_5712_);
    leanh::lean_dec_ref(v___y_5711_);
    return v_res_5717_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(
    mut v_xs_5718_: *mut leanh::LeanObject,
    mut v_e_5719_: *mut leanh::LeanObject,
    mut v___x_5720_: u8,
    mut v___x_5721_: u8,
    mut v_ys_5722_: *mut leanh::LeanObject,
    mut v_x_5723_: *mut leanh::LeanObject,
    mut v___y_5724_: *mut leanh::LeanObject,
    mut v___y_5725_: *mut leanh::LeanObject,
    mut v___y_5726_: *mut leanh::LeanObject,
    mut v___y_5727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: u8 = 0;
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5729_ = l_Array_append___redArg(v_xs_5718_, v_ys_5722_);
    v___x_5730_ = l_Lean_mkAppN(v_e_5719_, v_ys_5722_);
    v___x_5731_ = 1;
    v___x_5732_ = l_Lean_Meta_mkLambdaFVars(
        v___x_5729_,
        v___x_5730_,
        v___x_5720_,
        v___x_5721_,
        v___x_5720_,
        v___x_5721_,
        v___x_5731_,
        v___y_5724_,
        v___y_5725_,
        v___y_5726_,
        v___y_5727_,
    );
    leanh::lean_dec_ref(v___x_5729_);
    return v___x_5732_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed(
    mut v_xs_5733_: *mut leanh::LeanObject,
    mut v_e_5734_: *mut leanh::LeanObject,
    mut v___x_5735_: *mut leanh::LeanObject,
    mut v___x_5736_: *mut leanh::LeanObject,
    mut v_ys_5737_: *mut leanh::LeanObject,
    mut v_x_5738_: *mut leanh::LeanObject,
    mut v___y_5739_: *mut leanh::LeanObject,
    mut v___y_5740_: *mut leanh::LeanObject,
    mut v___y_5741_: *mut leanh::LeanObject,
    mut v___y_5742_: *mut leanh::LeanObject,
    mut v___y_5743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2271__boxed_5744_: u8 = 0;
    let mut v___x_2272__boxed_5745_: u8 = 0;
    let mut v_res_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2271__boxed_5744_ = (leanh::lean_unbox(v___x_5735_) as u8);
    v___x_2272__boxed_5745_ = (leanh::lean_unbox(v___x_5736_) as u8);
    v_res_5746_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(
        v_xs_5733_,
        v_e_5734_,
        v___x_2271__boxed_5744_,
        v___x_2272__boxed_5745_,
        v_ys_5737_,
        v_x_5738_,
        v___y_5739_,
        v___y_5740_,
        v___y_5741_,
        v___y_5742_,
    );
    leanh::lean_dec(v___y_5742_);
    leanh::lean_dec_ref(v___y_5741_);
    leanh::lean_dec(v___y_5740_);
    leanh::lean_dec_ref(v___y_5739_);
    leanh::lean_dec_ref(v_x_5738_);
    leanh::lean_dec_ref(v_ys_5737_);
    return v_res_5746_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(
    mut v___x_5747_: u8,
    mut v___x_5748_: u8,
    mut v_x_5749_: *mut leanh::LeanObject,
    mut v___y_5750_: *mut leanh::LeanObject,
    mut v___y_5751_: *mut leanh::LeanObject,
    mut v___y_5752_: *mut leanh::LeanObject,
    mut v___y_5753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5755_ = leanh::lean_unsigned_to_nat(1);
    v___x_5756_ = lean_mk_empty_array_with_capacity(v___x_5755_);
    leanh::lean_inc_ref(v_x_5749_);
    v___x_5757_ = lean_array_push(v___x_5756_, v_x_5749_);
    v___x_5758_ = l_Lean_Meta_mkLetFVars(
        v___x_5757_,
        v_x_5749_,
        v___x_5747_,
        v___x_5747_,
        v___x_5748_,
        v___y_5750_,
        v___y_5751_,
        v___y_5752_,
        v___y_5753_,
    );
    leanh::lean_dec_ref(v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed(
    mut v___x_5759_: *mut leanh::LeanObject,
    mut v___x_5760_: *mut leanh::LeanObject,
    mut v_x_5761_: *mut leanh::LeanObject,
    mut v___y_5762_: *mut leanh::LeanObject,
    mut v___y_5763_: *mut leanh::LeanObject,
    mut v___y_5764_: *mut leanh::LeanObject,
    mut v___y_5765_: *mut leanh::LeanObject,
    mut v___y_5766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2303__boxed_5767_: u8 = 0;
    let mut v___x_2304__boxed_5768_: u8 = 0;
    let mut v_res_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2303__boxed_5767_ = (leanh::lean_unbox(v___x_5759_) as u8);
    v___x_2304__boxed_5768_ = (leanh::lean_unbox(v___x_5760_) as u8);
    v_res_5769_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(
        v___x_2303__boxed_5767_,
        v___x_2304__boxed_5768_,
        v_x_5761_,
        v___y_5762_,
        v___y_5763_,
        v___y_5764_,
        v___y_5765_,
    );
    leanh::lean_dec(v___y_5765_);
    leanh::lean_dec_ref(v___y_5764_);
    leanh::lean_dec(v___y_5763_);
    leanh::lean_dec_ref(v___y_5762_);
    return v_res_5769_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2(
    mut v_numParams_5778_: *mut leanh::LeanObject,
    mut v_e_5779_: *mut leanh::LeanObject,
    mut v_xs_5780_: *mut leanh::LeanObject,
    mut v_body_5781_: *mut leanh::LeanObject,
    mut v___y_5782_: *mut leanh::LeanObject,
    mut v___y_5783_: *mut leanh::LeanObject,
    mut v___y_5784_: *mut leanh::LeanObject,
    mut v___y_5785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: u8 = 0;
    let mut v___x_5789_: u8 = 0;
    let mut v_lower_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: u8 = 0;
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u8 = 0;
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5814_: u8 = 0;
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5818_: u8 = 0;
    let mut v___x_5819_: u8 = 0;
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5824_: u8 = 0;
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: u8 = 0;
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5787_ = lean_array_get_size(v_xs_5780_);
                v___x_5788_ = lean_nat_dec_eq(v___x_5787_, v_numParams_5778_);
                if v___x_5788_ == 0 {
                    v___x_5789_ = 1;
                    v___x_5819_ = lean_nat_dec_lt(v_numParams_5778_, v___x_5787_);
                    if v___x_5819_ == 0 {
                        leanh::lean_dec_ref(v_body_5781_);
                        leanh::lean_inc(v___y_5785_);
                        leanh::lean_inc_ref(v___y_5784_);
                        leanh::lean_inc(v___y_5783_);
                        leanh::lean_inc_ref(v___y_5782_);
                        leanh::lean_inc_ref(v_e_5779_);
                        v___x_5820_ = lean_infer_type(
                            v_e_5779_,
                            v___y_5782_,
                            v___y_5783_,
                            v___y_5784_,
                            v___y_5785_,
                        );
                        if leanh::lean_obj_tag(v___x_5820_) == 0 {
                            v_a_5821_ = leanh::lean_ctor_get(v___x_5820_, 0);
                            v_isSharedCheck_5833_ =
                                (!leanh::lean_is_exclusive(v___x_5820_)) as u8;
                            if v_isSharedCheck_5833_ == 0 {
                                v___x_5823_ = v___x_5820_;
                                v_isShared_5824_ = v_isSharedCheck_5833_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5821_);
                                leanh::lean_dec(v___x_5820_);
                                v___x_5823_ = leanh::lean_box(0);
                                v_isShared_5824_ = v_isSharedCheck_5833_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_xs_5780_);
                            leanh::lean_dec_ref(v_e_5779_);
                            leanh::lean_dec(v_numParams_5778_);
                            return v___x_5820_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5779_);
                        v___x_5834_ = leanh::lean_unsigned_to_nat(0);
                        v___x_5835_ = lean_nat_dec_le(v_numParams_5778_, v___x_5834_);
                        if v___x_5835_ == 0 {
                            leanh::lean_inc(v_numParams_5778_);
                            v_lower_5791_ = v_numParams_5778_;
                            v_upper_5792_ = v___x_5787_;
                            state = 1;
                            continue;
                        } else {
                            v_lower_5791_ = v___x_5834_;
                            v_upper_5792_ = v___x_5787_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_body_5781_);
                    leanh::lean_dec_ref(v_xs_5780_);
                    leanh::lean_dec(v_numParams_5778_);
                    v___x_5836_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5836_, 0, v_e_5779_);
                    return v___x_5836_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_xs_5780_);
                v___x_5793_ = l_Array_toSubarray___redArg(v_xs_5780_, v_lower_5791_, v_upper_5792_);
                v___x_5794_ = l_Subarray_copy___redArg(v___x_5793_);
                v___x_5795_ = 1;
                v___x_5796_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_5794_,
                    v_body_5781_,
                    v___x_5788_,
                    v___x_5789_,
                    v___x_5788_,
                    v___x_5789_,
                    v___x_5795_,
                    v___y_5782_,
                    v___y_5783_,
                    v___y_5784_,
                    v___y_5785_,
                );
                leanh::lean_dec_ref(v___x_5794_);
                if leanh::lean_obj_tag(v___x_5796_) == 0 {
                    v_a_5797_ = leanh::lean_ctor_get(v___x_5796_, 0);
                    leanh::lean_inc(v_a_5797_);
                    leanh::lean_dec_ref_known(v___x_5796_, 1);
                    v___x_5798_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1;
                    v___x_5799_ =
                        l_Lean_Core_mkFreshUserName(v___x_5798_, v___y_5784_, v___y_5785_);
                    if leanh::lean_obj_tag(v___x_5799_) == 0 {
                        v_a_5800_ = leanh::lean_ctor_get(v___x_5799_, 0);
                        leanh::lean_inc(v_a_5800_);
                        leanh::lean_dec_ref_known(v___x_5799_, 1);
                        leanh::lean_inc(v___y_5785_);
                        leanh::lean_inc_ref(v___y_5784_);
                        leanh::lean_inc(v___y_5783_);
                        leanh::lean_inc_ref(v___y_5782_);
                        leanh::lean_inc(v_a_5797_);
                        v___x_5801_ = lean_infer_type(
                            v_a_5797_,
                            v___y_5782_,
                            v___y_5783_,
                            v___y_5784_,
                            v___y_5785_,
                        );
                        if leanh::lean_obj_tag(v___x_5801_) == 0 {
                            v_a_5802_ = leanh::lean_ctor_get(v___x_5801_, 0);
                            leanh::lean_inc(v_a_5802_);
                            leanh::lean_dec_ref_known(v___x_5801_, 1);
                            v___f_5803_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__2;
                            v___x_5804_ = 0;
                            v___x_5805_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(v_a_5800_, v_a_5802_, v_a_5797_, v___f_5803_, v___x_5788_, v___x_5804_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
                            if leanh::lean_obj_tag(v___x_5805_) == 0 {
                                v_a_5806_ = leanh::lean_ctor_get(v___x_5805_, 0);
                                leanh::lean_inc(v_a_5806_);
                                leanh::lean_dec_ref_known(v___x_5805_, 1);
                                v___x_5807_ = leanh::lean_unsigned_to_nat(0);
                                v___x_5808_ = l_Array_toSubarray___redArg(
                                    v_xs_5780_,
                                    v___x_5807_,
                                    v_numParams_5778_,
                                );
                                v___x_5809_ = l_Subarray_copy___redArg(v___x_5808_);
                                v___x_5810_ = l_Lean_Meta_mkLambdaFVars(
                                    v___x_5809_,
                                    v_a_5806_,
                                    v___x_5788_,
                                    v___x_5789_,
                                    v___x_5788_,
                                    v___x_5789_,
                                    v___x_5795_,
                                    v___y_5782_,
                                    v___y_5783_,
                                    v___y_5784_,
                                    v___y_5785_,
                                );
                                leanh::lean_dec_ref(v___x_5809_);
                                return v___x_5810_;
                            } else {
                                leanh::lean_dec_ref(v_xs_5780_);
                                leanh::lean_dec(v_numParams_5778_);
                                return v___x_5805_;
                            }
                        } else {
                            leanh::lean_dec(v_a_5800_);
                            leanh::lean_dec(v_a_5797_);
                            leanh::lean_dec_ref(v_xs_5780_);
                            leanh::lean_dec(v_numParams_5778_);
                            return v___x_5801_;
                        }
                    } else {
                        leanh::lean_dec(v_a_5797_);
                        leanh::lean_dec_ref(v_xs_5780_);
                        leanh::lean_dec(v_numParams_5778_);
                        v_a_5811_ = leanh::lean_ctor_get(v___x_5799_, 0);
                        v_isSharedCheck_5818_ =
                            (!leanh::lean_is_exclusive(v___x_5799_)) as u8;
                        if v_isSharedCheck_5818_ == 0 {
                            v___x_5813_ = v___x_5799_;
                            v_isShared_5814_ = v_isSharedCheck_5818_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5811_);
                            leanh::lean_dec(v___x_5799_);
                            v___x_5813_ = leanh::lean_box(0);
                            v_isShared_5814_ = v_isSharedCheck_5818_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_xs_5780_);
                    leanh::lean_dec(v_numParams_5778_);
                    return v___x_5796_;
                }
            }
            2 => {
                if v_isShared_5814_ == 0 {
                    v___x_5816_ = v___x_5813_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5817_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
                    v___x_5816_ = v_reuseFailAlloc_5817_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5816_;
            }
            4 => {
                v___x_5825_ = leanh::lean_box((v___x_5788_) as usize);
                v___x_5826_ = leanh::lean_box((v___x_5789_) as usize);
                v___f_5827_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                leanh::lean_closure_set(v___f_5827_, 0, v_xs_5780_);
                leanh::lean_closure_set(v___f_5827_, 1, v_e_5779_);
                leanh::lean_closure_set(v___f_5827_, 2, v___x_5825_);
                leanh::lean_closure_set(v___f_5827_, 3, v___x_5826_);
                v___x_5828_ = lean_nat_sub(v_numParams_5778_, v___x_5787_);
                leanh::lean_dec(v_numParams_5778_);
                if v_isShared_5824_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5823_, 1);
                    leanh::lean_ctor_set(v___x_5823_, 0, v___x_5828_);
                    v___x_5830_ = v___x_5823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5828_);
                    v___x_5830_ = v_reuseFailAlloc_5832_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5831_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(v_a_5821_, v___x_5830_, v___f_5827_, v___x_5788_, v___x_5788_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
                return v___x_5831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___boxed(
    mut v_numParams_5837_: *mut leanh::LeanObject,
    mut v_e_5838_: *mut leanh::LeanObject,
    mut v_xs_5839_: *mut leanh::LeanObject,
    mut v_body_5840_: *mut leanh::LeanObject,
    mut v___y_5841_: *mut leanh::LeanObject,
    mut v___y_5842_: *mut leanh::LeanObject,
    mut v___y_5843_: *mut leanh::LeanObject,
    mut v___y_5844_: *mut leanh::LeanObject,
    mut v___y_5845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5846_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2(
        v_numParams_5837_,
        v_e_5838_,
        v_xs_5839_,
        v_body_5840_,
        v___y_5841_,
        v___y_5842_,
        v___y_5843_,
        v___y_5844_,
    );
    leanh::lean_dec(v___y_5844_);
    leanh::lean_dec_ref(v___y_5843_);
    leanh::lean_dec(v___y_5842_);
    leanh::lean_dec_ref(v___y_5841_);
    return v_res_5846_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(
    mut v_e_5847_: *mut leanh::LeanObject,
    mut v_numParams_5848_: *mut leanh::LeanObject,
    mut v_a_5849_: *mut leanh::LeanObject,
    mut v_a_5850_: *mut leanh::LeanObject,
    mut v_a_5851_: *mut leanh::LeanObject,
    mut v_a_5852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: u8 = 0;
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_e_5847_);
    v___f_5854_ = leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___f_5854_, 0, v_numParams_5848_);
    leanh::lean_closure_set(v___f_5854_, 1, v_e_5847_);
    v___x_5855_ = 0;
    v___x_5856_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___redArg(v_e_5847_, v___f_5854_, v___x_5855_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_);
    return v___x_5856_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___boxed(
    mut v_e_5857_: *mut leanh::LeanObject,
    mut v_numParams_5858_: *mut leanh::LeanObject,
    mut v_a_5859_: *mut leanh::LeanObject,
    mut v_a_5860_: *mut leanh::LeanObject,
    mut v_a_5861_: *mut leanh::LeanObject,
    mut v_a_5862_: *mut leanh::LeanObject,
    mut v_a_5863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5864_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(
        v_e_5857_,
        v_numParams_5858_,
        v_a_5859_,
        v_a_5860_,
        v_a_5861_,
        v_a_5862_,
    );
    leanh::lean_dec(v_a_5862_);
    leanh::lean_dec_ref(v_a_5861_);
    leanh::lean_dec(v_a_5860_);
    leanh::lean_dec_ref(v_a_5859_);
    return v_res_5864_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_5865_: *mut leanh::LeanObject,
    mut v___y_5866_: *mut leanh::LeanObject,
    mut v___y_5867_: *mut leanh::LeanObject,
    mut v___y_5868_: *mut leanh::LeanObject,
    mut v___y_5869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5871_ = lean_st_ref_get(v___y_5869_);
    v_env_5872_ = leanh::lean_ctor_get(v___x_5871_, 0);
    leanh::lean_inc_ref(v_env_5872_);
    leanh::lean_dec(v___x_5871_);
    v___x_5873_ = lean_st_ref_get(v___y_5867_);
    v_mctx_5874_ = leanh::lean_ctor_get(v___x_5873_, 0);
    leanh::lean_inc_ref(v_mctx_5874_);
    leanh::lean_dec(v___x_5873_);
    v_lctx_5875_ = leanh::lean_ctor_get(v___y_5866_, 2);
    v_options_5876_ = leanh::lean_ctor_get(v___y_5868_, 2);
    leanh::lean_inc_ref(v_options_5876_);
    leanh::lean_inc_ref(v_lctx_5875_);
    v___x_5877_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5877_, 0, v_env_5872_);
    leanh::lean_ctor_set(v___x_5877_, 1, v_mctx_5874_);
    leanh::lean_ctor_set(v___x_5877_, 2, v_lctx_5875_);
    leanh::lean_ctor_set(v___x_5877_, 3, v_options_5876_);
    v___x_5878_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5878_, 0, v___x_5877_);
    leanh::lean_ctor_set(v___x_5878_, 1, v_msgData_5865_);
    v___x_5879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5879_, 0, v___x_5878_);
    return v___x_5879_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
    mut v___y_5885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5886_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_);
    leanh::lean_dec(v___y_5884_);
    leanh::lean_dec_ref(v___y_5883_);
    leanh::lean_dec(v___y_5882_);
    leanh::lean_dec_ref(v___y_5881_);
    return v_res_5886_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_5887_: *mut leanh::LeanObject,
    mut v___y_5888_: *mut leanh::LeanObject,
    mut v___y_5889_: *mut leanh::LeanObject,
    mut v___y_5890_: *mut leanh::LeanObject,
    mut v___y_5891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5893_ = leanh::lean_ctor_get(v___y_5890_, 5);
                v___x_5894_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
                v_a_5895_ = leanh::lean_ctor_get(v___x_5894_, 0);
                v_isSharedCheck_5903_ = (!leanh::lean_is_exclusive(v___x_5894_)) as u8;
                if v_isSharedCheck_5903_ == 0 {
                    v___x_5897_ = v___x_5894_;
                    v_isShared_5898_ = v_isSharedCheck_5903_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5895_);
                    leanh::lean_dec(v___x_5894_);
                    v___x_5897_ = leanh::lean_box(0);
                    v_isShared_5898_ = v_isSharedCheck_5903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_5893_);
                v___x_5899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5899_, 0, v_ref_5893_);
                leanh::lean_ctor_set(v___x_5899_, 1, v_a_5895_);
                if v_isShared_5898_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5897_, 1);
                    leanh::lean_ctor_set(v___x_5897_, 0, v___x_5899_);
                    v___x_5901_ = v___x_5897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5902_, 0, v___x_5899_);
                    v___x_5901_ = v_reuseFailAlloc_5902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_5904_: *mut leanh::LeanObject,
    mut v___y_5905_: *mut leanh::LeanObject,
    mut v___y_5906_: *mut leanh::LeanObject,
    mut v___y_5907_: *mut leanh::LeanObject,
    mut v___y_5908_: *mut leanh::LeanObject,
    mut v___y_5909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5910_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
    leanh::lean_dec(v___y_5908_);
    leanh::lean_dec_ref(v___y_5907_);
    leanh::lean_dec(v___y_5906_);
    leanh::lean_dec_ref(v___y_5905_);
    return v_res_5910_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_5911_: *mut leanh::LeanObject,
    mut v_msg_5912_: *mut leanh::LeanObject,
    mut v___y_5913_: *mut leanh::LeanObject,
    mut v___y_5914_: *mut leanh::LeanObject,
    mut v___y_5915_: *mut leanh::LeanObject,
    mut v___y_5916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5930_: u8 = 0;
    let mut v_cancelTk_x3f_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5932_: u8 = 0;
    let mut v_inheritedTraceOptions_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5918_ = leanh::lean_ctor_get(v___y_5915_, 0);
    v_fileMap_5919_ = leanh::lean_ctor_get(v___y_5915_, 1);
    v_options_5920_ = leanh::lean_ctor_get(v___y_5915_, 2);
    v_currRecDepth_5921_ = leanh::lean_ctor_get(v___y_5915_, 3);
    v_maxRecDepth_5922_ = leanh::lean_ctor_get(v___y_5915_, 4);
    v_ref_5923_ = leanh::lean_ctor_get(v___y_5915_, 5);
    v_currNamespace_5924_ = leanh::lean_ctor_get(v___y_5915_, 6);
    v_openDecls_5925_ = leanh::lean_ctor_get(v___y_5915_, 7);
    v_initHeartbeats_5926_ = leanh::lean_ctor_get(v___y_5915_, 8);
    v_maxHeartbeats_5927_ = leanh::lean_ctor_get(v___y_5915_, 9);
    v_quotContext_5928_ = leanh::lean_ctor_get(v___y_5915_, 10);
    v_currMacroScope_5929_ = leanh::lean_ctor_get(v___y_5915_, 11);
    v_diag_5930_ = leanh::lean_ctor_get_uint8(
        v___y_5915_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5931_ = leanh::lean_ctor_get(v___y_5915_, 12);
    v_suppressElabErrors_5932_ = leanh::lean_ctor_get_uint8(
        v___y_5915_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5933_ = leanh::lean_ctor_get(v___y_5915_, 13);
    v_ref_5934_ = l_Lean_replaceRef(v_ref_5911_, v_ref_5923_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5933_);
    leanh::lean_inc(v_cancelTk_x3f_5931_);
    leanh::lean_inc(v_currMacroScope_5929_);
    leanh::lean_inc(v_quotContext_5928_);
    leanh::lean_inc(v_maxHeartbeats_5927_);
    leanh::lean_inc(v_initHeartbeats_5926_);
    leanh::lean_inc(v_openDecls_5925_);
    leanh::lean_inc(v_currNamespace_5924_);
    leanh::lean_inc(v_maxRecDepth_5922_);
    leanh::lean_inc(v_currRecDepth_5921_);
    leanh::lean_inc_ref(v_options_5920_);
    leanh::lean_inc_ref(v_fileMap_5919_);
    leanh::lean_inc_ref(v_fileName_5918_);
    v___x_5935_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5935_, 0, v_fileName_5918_);
    leanh::lean_ctor_set(v___x_5935_, 1, v_fileMap_5919_);
    leanh::lean_ctor_set(v___x_5935_, 2, v_options_5920_);
    leanh::lean_ctor_set(v___x_5935_, 3, v_currRecDepth_5921_);
    leanh::lean_ctor_set(v___x_5935_, 4, v_maxRecDepth_5922_);
    leanh::lean_ctor_set(v___x_5935_, 5, v_ref_5934_);
    leanh::lean_ctor_set(v___x_5935_, 6, v_currNamespace_5924_);
    leanh::lean_ctor_set(v___x_5935_, 7, v_openDecls_5925_);
    leanh::lean_ctor_set(v___x_5935_, 8, v_initHeartbeats_5926_);
    leanh::lean_ctor_set(v___x_5935_, 9, v_maxHeartbeats_5927_);
    leanh::lean_ctor_set(v___x_5935_, 10, v_quotContext_5928_);
    leanh::lean_ctor_set(v___x_5935_, 11, v_currMacroScope_5929_);
    leanh::lean_ctor_set(v___x_5935_, 12, v_cancelTk_x3f_5931_);
    leanh::lean_ctor_set(v___x_5935_, 13, v_inheritedTraceOptions_5933_);
    leanh::lean_ctor_set_uint8(
        v___x_5935_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5930_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5935_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5932_,
    );
    v___x_5936_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_5912_, v___y_5913_, v___y_5914_, v___x_5935_, v___y_5916_);
    leanh::lean_dec_ref_known(v___x_5935_, 14);
    return v___x_5936_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_5937_: *mut leanh::LeanObject,
    mut v_msg_5938_: *mut leanh::LeanObject,
    mut v___y_5939_: *mut leanh::LeanObject,
    mut v___y_5940_: *mut leanh::LeanObject,
    mut v___y_5941_: *mut leanh::LeanObject,
    mut v___y_5942_: *mut leanh::LeanObject,
    mut v___y_5943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5944_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_5937_, v_msg_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
    leanh::lean_dec(v___y_5942_);
    leanh::lean_dec_ref(v___y_5941_);
    leanh::lean_dec(v___y_5940_);
    leanh::lean_dec_ref(v___y_5939_);
    leanh::lean_dec(v_ref_5937_);
    return v_res_5944_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_5945_: *mut leanh::LeanObject,
    mut v_declHint_5946_: *mut leanh::LeanObject,
    mut v___y_5947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: u8 = 0;
    let mut v_isExporting_5952_: u8 = 0;
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5976_: u8 = 0;
    let mut v___x_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6008_: u8 = 0;
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5949_ = lean_st_ref_get(v___y_5947_);
                v_env_5950_ = leanh::lean_ctor_get(v___x_5949_, 0);
                leanh::lean_inc_ref(v_env_5950_);
                leanh::lean_dec(v___x_5949_);
                v___x_5951_ = l_Lean_Name_isAnonymous(v_declHint_5946_);
                if v___x_5951_ == 0 {
                    v_isExporting_5952_ = leanh::lean_ctor_get_uint8(
                        v_env_5950_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5952_ == 0 {
                        leanh::lean_dec_ref(v_env_5950_);
                        leanh::lean_dec(v_declHint_5946_);
                        v___x_5953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5953_, 0, v_msg_5945_);
                        return v___x_5953_;
                    } else {
                        leanh::lean_inc_ref(v_env_5950_);
                        v___x_5954_ = l_Lean_Environment_setExporting(v_env_5950_, v___x_5951_);
                        leanh::lean_inc(v_declHint_5946_);
                        leanh::lean_inc_ref(v___x_5954_);
                        v___x_5955_ = l_Lean_Environment_contains(
                            v___x_5954_,
                            v_declHint_5946_,
                            v_isExporting_5952_,
                        );
                        if v___x_5955_ == 0 {
                            leanh::lean_dec_ref(v___x_5954_);
                            leanh::lean_dec_ref(v_env_5950_);
                            leanh::lean_dec(v_declHint_5946_);
                            v___x_5956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5956_, 0, v_msg_5945_);
                            return v___x_5956_;
                        } else {
                            v___x_5957_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2);
                            v___x_5958_ = leanh::lean_unsigned_to_nat(32);
                            v___x_5959_ = lean_mk_empty_array_with_capacity(v___x_5958_);
                            leanh::lean_dec_ref(v___x_5959_);
                            v___x_5960_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__5);
                            v___x_5961_ = l_Lean_Options_empty;
                            v___x_5962_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_5962_, 0, v___x_5954_);
                            leanh::lean_ctor_set(v___x_5962_, 1, v___x_5957_);
                            leanh::lean_ctor_set(v___x_5962_, 2, v___x_5960_);
                            leanh::lean_ctor_set(v___x_5962_, 3, v___x_5961_);
                            leanh::lean_inc(v_declHint_5946_);
                            v___x_5963_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5946_, v___x_5951_);
                            v_c_5964_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_5964_, 0, v___x_5962_);
                            leanh::lean_ctor_set(v_c_5964_, 1, v___x_5963_);
                            v___x_5965_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5950_,
                                v_declHint_5946_,
                            );
                            if leanh::lean_obj_tag(v___x_5965_) == 0 {
                                leanh::lean_dec_ref(v_env_5950_);
                                leanh::lean_dec(v_declHint_5946_);
                                v___x_5966_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1);
                                v___x_5967_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5967_, 0, v___x_5966_);
                                leanh::lean_ctor_set(v___x_5967_, 1, v_c_5964_);
                                v___x_5968_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__3);
                                v___x_5969_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5969_, 0, v___x_5967_);
                                leanh::lean_ctor_set(v___x_5969_, 1, v___x_5968_);
                                v___x_5970_ = l_Lean_MessageData_note(v___x_5969_);
                                v___x_5971_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5971_, 0, v_msg_5945_);
                                leanh::lean_ctor_set(v___x_5971_, 1, v___x_5970_);
                                v___x_5972_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5972_, 0, v___x_5971_);
                                return v___x_5972_;
                            } else {
                                v_val_5973_ = leanh::lean_ctor_get(v___x_5965_, 0);
                                v_isSharedCheck_6008_ =
                                    (!leanh::lean_is_exclusive(v___x_5965_)) as u8;
                                if v_isSharedCheck_6008_ == 0 {
                                    v___x_5975_ = v___x_5965_;
                                    v_isShared_5976_ = v_isSharedCheck_6008_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_5973_);
                                    leanh::lean_dec(v___x_5965_);
                                    v___x_5975_ = leanh::lean_box(0);
                                    v_isShared_5976_ = v_isSharedCheck_6008_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_5950_);
                    leanh::lean_dec(v_declHint_5946_);
                    v___x_6009_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6009_, 0, v_msg_5945_);
                    return v___x_6009_;
                }
            }
            1 => {
                v___x_5977_ = leanh::lean_box(0);
                v___x_5978_ = l_Lean_Environment_header(v_env_5950_);
                leanh::lean_dec_ref(v_env_5950_);
                v___x_5979_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5978_);
                v_mod_5980_ = lean_array_get(v___x_5977_, v___x_5979_, v_val_5973_);
                leanh::lean_dec(v_val_5973_);
                leanh::lean_dec_ref(v___x_5979_);
                v___x_5981_ = l_Lean_isPrivateName(v_declHint_5946_);
                leanh::lean_dec(v_declHint_5946_);
                if v___x_5981_ == 0 {
                    v___x_5982_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__5);
                    v___x_5983_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5983_, 0, v___x_5982_);
                    leanh::lean_ctor_set(v___x_5983_, 1, v_c_5964_);
                    v___x_5984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__7);
                    v___x_5985_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5985_, 0, v___x_5983_);
                    leanh::lean_ctor_set(v___x_5985_, 1, v___x_5984_);
                    v___x_5986_ = l_Lean_MessageData_ofName(v_mod_5980_);
                    v___x_5987_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5987_, 0, v___x_5985_);
                    leanh::lean_ctor_set(v___x_5987_, 1, v___x_5986_);
                    v___x_5988_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__9);
                    v___x_5989_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5989_, 0, v___x_5987_);
                    leanh::lean_ctor_set(v___x_5989_, 1, v___x_5988_);
                    v___x_5990_ = l_Lean_MessageData_note(v___x_5989_);
                    v___x_5991_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5991_, 0, v_msg_5945_);
                    leanh::lean_ctor_set(v___x_5991_, 1, v___x_5990_);
                    if v_isShared_5976_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5975_, 0);
                        leanh::lean_ctor_set(v___x_5975_, 0, v___x_5991_);
                        v___x_5993_ = v___x_5975_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5994_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5994_, 0, v___x_5991_);
                        v___x_5993_ = v_reuseFailAlloc_5994_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5995_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__1);
                    v___x_5996_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5996_, 0, v___x_5995_);
                    leanh::lean_ctor_set(v___x_5996_, 1, v_c_5964_);
                    v___x_5997_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__11);
                    v___x_5998_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5998_, 0, v___x_5996_);
                    leanh::lean_ctor_set(v___x_5998_, 1, v___x_5997_);
                    v___x_5999_ = l_Lean_MessageData_ofName(v_mod_5980_);
                    v___x_6000_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6000_, 0, v___x_5998_);
                    leanh::lean_ctor_set(v___x_6000_, 1, v___x_5999_);
                    v___x_6001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__5_spec__14___redArg___closed__13);
                    v___x_6002_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6002_, 0, v___x_6000_);
                    leanh::lean_ctor_set(v___x_6002_, 1, v___x_6001_);
                    v___x_6003_ = l_Lean_MessageData_note(v___x_6002_);
                    v___x_6004_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6004_, 0, v_msg_5945_);
                    leanh::lean_ctor_set(v___x_6004_, 1, v___x_6003_);
                    if v_isShared_5976_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5975_, 0);
                        leanh::lean_ctor_set(v___x_5975_, 0, v___x_6004_);
                        v___x_6006_ = v___x_5975_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_6004_);
                        v___x_6006_ = v_reuseFailAlloc_6007_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5993_;
            }
            3 => {
                return v___x_6006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_6010_: *mut leanh::LeanObject,
    mut v_declHint_6011_: *mut leanh::LeanObject,
    mut v___y_6012_: *mut leanh::LeanObject,
    mut v___y_6013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6014_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_6010_, v_declHint_6011_, v___y_6012_);
    leanh::lean_dec(v___y_6012_);
    return v_res_6014_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_6015_: *mut leanh::LeanObject,
    mut v_declHint_6016_: *mut leanh::LeanObject,
    mut v___y_6017_: *mut leanh::LeanObject,
    mut v___y_6018_: *mut leanh::LeanObject,
    mut v___y_6019_: *mut leanh::LeanObject,
    mut v___y_6020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6026_: u8 = 0;
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6022_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_6015_, v_declHint_6016_, v___y_6020_);
                v_a_6023_ = leanh::lean_ctor_get(v___x_6022_, 0);
                v_isSharedCheck_6032_ = (!leanh::lean_is_exclusive(v___x_6022_)) as u8;
                if v_isSharedCheck_6032_ == 0 {
                    v___x_6025_ = v___x_6022_;
                    v_isShared_6026_ = v_isSharedCheck_6032_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6023_);
                    leanh::lean_dec(v___x_6022_);
                    v___x_6025_ = leanh::lean_box(0);
                    v_isShared_6026_ = v_isSharedCheck_6032_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6027_ = l_Lean_unknownIdentifierMessageTag;
                v___x_6028_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6028_, 0, v___x_6027_);
                leanh::lean_ctor_set(v___x_6028_, 1, v_a_6023_);
                if v_isShared_6026_ == 0 {
                    leanh::lean_ctor_set(v___x_6025_, 0, v___x_6028_);
                    v___x_6030_ = v___x_6025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_6028_);
                    v___x_6030_ = v_reuseFailAlloc_6031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_6033_: *mut leanh::LeanObject,
    mut v_declHint_6034_: *mut leanh::LeanObject,
    mut v___y_6035_: *mut leanh::LeanObject,
    mut v___y_6036_: *mut leanh::LeanObject,
    mut v___y_6037_: *mut leanh::LeanObject,
    mut v___y_6038_: *mut leanh::LeanObject,
    mut v___y_6039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6040_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_6033_, v_declHint_6034_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
    leanh::lean_dec(v___y_6038_);
    leanh::lean_dec_ref(v___y_6037_);
    leanh::lean_dec(v___y_6036_);
    leanh::lean_dec_ref(v___y_6035_);
    return v_res_6040_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_6041_: *mut leanh::LeanObject,
    mut v_msg_6042_: *mut leanh::LeanObject,
    mut v_declHint_6043_: *mut leanh::LeanObject,
    mut v___y_6044_: *mut leanh::LeanObject,
    mut v___y_6045_: *mut leanh::LeanObject,
    mut v___y_6046_: *mut leanh::LeanObject,
    mut v___y_6047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6049_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_6042_, v_declHint_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_);
    v_a_6050_ = leanh::lean_ctor_get(v___x_6049_, 0);
    leanh::lean_inc(v_a_6050_);
    leanh::lean_dec_ref(v___x_6049_);
    v___x_6051_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_6041_, v_a_6050_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_);
    return v___x_6051_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_6052_: *mut leanh::LeanObject,
    mut v_msg_6053_: *mut leanh::LeanObject,
    mut v_declHint_6054_: *mut leanh::LeanObject,
    mut v___y_6055_: *mut leanh::LeanObject,
    mut v___y_6056_: *mut leanh::LeanObject,
    mut v___y_6057_: *mut leanh::LeanObject,
    mut v___y_6058_: *mut leanh::LeanObject,
    mut v___y_6059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_6052_, v_msg_6053_, v_declHint_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_);
    leanh::lean_dec(v___y_6058_);
    leanh::lean_dec_ref(v___y_6057_);
    leanh::lean_dec(v___y_6056_);
    leanh::lean_dec_ref(v___y_6055_);
    leanh::lean_dec(v_ref_6052_);
    return v_res_6060_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1___redArg(
    mut v_ref_6061_: *mut leanh::LeanObject,
    mut v_constName_6062_: *mut leanh::LeanObject,
    mut v___y_6063_: *mut leanh::LeanObject,
    mut v___y_6064_: *mut leanh::LeanObject,
    mut v___y_6065_: *mut leanh::LeanObject,
    mut v___y_6066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: u8 = 0;
    let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6068_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_6069_ = 0;
    leanh::lean_inc(v_constName_6062_);
    v___x_6070_ = l_Lean_MessageData_ofConstName(v_constName_6062_, v___x_6069_);
    v___x_6071_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6071_, 0, v___x_6068_);
    leanh::lean_ctor_set(v___x_6071_, 1, v___x_6070_);
    v___x_6072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_6073_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6073_, 0, v___x_6071_);
    leanh::lean_ctor_set(v___x_6073_, 1, v___x_6072_);
    v___x_6074_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_6061_, v___x_6073_, v_constName_6062_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
    return v___x_6074_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_6075_: *mut leanh::LeanObject,
    mut v_constName_6076_: *mut leanh::LeanObject,
    mut v___y_6077_: *mut leanh::LeanObject,
    mut v___y_6078_: *mut leanh::LeanObject,
    mut v___y_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6082_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1___redArg(v_ref_6075_, v_constName_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    leanh::lean_dec(v___y_6080_);
    leanh::lean_dec_ref(v___y_6079_);
    leanh::lean_dec(v___y_6078_);
    leanh::lean_dec_ref(v___y_6077_);
    leanh::lean_dec(v_ref_6075_);
    return v_res_6082_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0___redArg(
    mut v_constName_6083_: *mut leanh::LeanObject,
    mut v___y_6084_: *mut leanh::LeanObject,
    mut v___y_6085_: *mut leanh::LeanObject,
    mut v___y_6086_: *mut leanh::LeanObject,
    mut v___y_6087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6089_ = leanh::lean_ctor_get(v___y_6086_, 5);
    v___x_6090_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1___redArg(v_ref_6089_, v_constName_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
    return v___x_6090_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0___redArg___boxed(
    mut v_constName_6091_: *mut leanh::LeanObject,
    mut v___y_6092_: *mut leanh::LeanObject,
    mut v___y_6093_: *mut leanh::LeanObject,
    mut v___y_6094_: *mut leanh::LeanObject,
    mut v___y_6095_: *mut leanh::LeanObject,
    mut v___y_6096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6097_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0___redArg(v_constName_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
    leanh::lean_dec(v___y_6095_);
    leanh::lean_dec_ref(v___y_6094_);
    leanh::lean_dec(v___y_6093_);
    leanh::lean_dec_ref(v___y_6092_);
    return v_res_6097_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0(
    mut v_constName_6098_: *mut leanh::LeanObject,
    mut v___y_6099_: *mut leanh::LeanObject,
    mut v___y_6100_: *mut leanh::LeanObject,
    mut v___y_6101_: *mut leanh::LeanObject,
    mut v___y_6102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: u8 = 0;
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6112_: u8 = 0;
    let mut v___x_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6104_ = lean_st_ref_get(v___y_6102_);
                v_env_6105_ = leanh::lean_ctor_get(v___x_6104_, 0);
                leanh::lean_inc_ref(v_env_6105_);
                leanh::lean_dec(v___x_6104_);
                v___x_6106_ = 0;
                leanh::lean_inc(v_constName_6098_);
                v___x_6107_ =
                    l_Lean_Environment_find_x3f(v_env_6105_, v_constName_6098_, v___x_6106_);
                if leanh::lean_obj_tag(v___x_6107_) == 0 {
                    v___x_6108_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0___redArg(v_constName_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
                    return v___x_6108_;
                } else {
                    leanh::lean_dec(v_constName_6098_);
                    v_val_6109_ = leanh::lean_ctor_get(v___x_6107_, 0);
                    v_isSharedCheck_6116_ = (!leanh::lean_is_exclusive(v___x_6107_)) as u8;
                    if v_isSharedCheck_6116_ == 0 {
                        v___x_6111_ = v___x_6107_;
                        v_isShared_6112_ = v_isSharedCheck_6116_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6109_);
                        leanh::lean_dec(v___x_6107_);
                        v___x_6111_ = leanh::lean_box(0);
                        v_isShared_6112_ = v_isSharedCheck_6116_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6112_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6111_, 0);
                    v___x_6114_ = v___x_6111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 0, v_val_6109_);
                    v___x_6114_ = v_reuseFailAlloc_6115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0___boxed(
    mut v_constName_6117_: *mut leanh::LeanObject,
    mut v___y_6118_: *mut leanh::LeanObject,
    mut v___y_6119_: *mut leanh::LeanObject,
    mut v___y_6120_: *mut leanh::LeanObject,
    mut v___y_6121_: *mut leanh::LeanObject,
    mut v___y_6122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6123_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0(v_constName_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
    leanh::lean_dec(v___y_6121_);
    leanh::lean_dec_ref(v___y_6120_);
    leanh::lean_dec(v___y_6119_);
    leanh::lean_dec_ref(v___y_6118_);
    return v_res_6123_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed(
    mut v_i_6127_: *mut leanh::LeanObject,
    mut v_args_6128_: *mut leanh::LeanObject,
    mut v_altIdx_6129_: *mut leanh::LeanObject,
    mut v_letFVars_6130_: *mut leanh::LeanObject,
    mut v_declName_6131_: *mut leanh::LeanObject,
    mut v_us_6132_: *mut leanh::LeanObject,
    mut v_info_6133_: *mut leanh::LeanObject,
    mut v_altNumParams_6134_: *mut leanh::LeanObject,
    mut v_altFVar_6135_: *mut leanh::LeanObject,
    mut v___y_6136_: *mut leanh::LeanObject,
    mut v___y_6137_: *mut leanh::LeanObject,
    mut v___y_6138_: *mut leanh::LeanObject,
    mut v___y_6139_: *mut leanh::LeanObject,
    mut v___y_6140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6141_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(v_i_6127_, v_args_6128_, v_altIdx_6129_, v_letFVars_6130_, v_declName_6131_, v_us_6132_, v_info_6133_, v_altNumParams_6134_, v_altFVar_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_);
    leanh::lean_dec(v___y_6139_);
    leanh::lean_dec_ref(v___y_6138_);
    leanh::lean_dec(v___y_6137_);
    leanh::lean_dec_ref(v___y_6136_);
    leanh::lean_dec(v_altIdx_6129_);
    leanh::lean_dec(v_i_6127_);
    return v_res_6141_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(
    mut v_declName_6142_: *mut leanh::LeanObject,
    mut v_us_6143_: *mut leanh::LeanObject,
    mut v_info_6144_: *mut leanh::LeanObject,
    mut v_altNumParams_6145_: *mut leanh::LeanObject,
    mut v_i_6146_: *mut leanh::LeanObject,
    mut v_args_6147_: *mut leanh::LeanObject,
    mut v_letFVars_6148_: *mut leanh::LeanObject,
    mut v_a_6149_: *mut leanh::LeanObject,
    mut v_a_6150_: *mut leanh::LeanObject,
    mut v_a_6151_: *mut leanh::LeanObject,
    mut v_a_6152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: u8 = 0;
    let mut v___x_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: u8 = 0;
    let mut v___x_6162_: u8 = 0;
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6167_: u8 = 0;
    let mut v___x_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6171_: u8 = 0;
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_altIdx_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: u8 = 0;
    let mut v___x_6186_: u8 = 0;
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6154_ = lean_array_get_size(v_altNumParams_6145_);
                v___x_6155_ = lean_nat_dec_lt(v_i_6146_, v___x_6154_);
                if v___x_6155_ == 0 {
                    leanh::lean_dec(v_i_6146_);
                    leanh::lean_dec_ref(v_altNumParams_6145_);
                    leanh::lean_dec_ref(v_info_6144_);
                    v___x_6156_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0(v_declName_6142_, v_a_6149_, v_a_6150_, v_a_6151_, v_a_6152_);
                    if leanh::lean_obj_tag(v___x_6156_) == 0 {
                        v_a_6157_ = leanh::lean_ctor_get(v___x_6156_, 0);
                        leanh::lean_inc(v_a_6157_);
                        leanh::lean_dec_ref_known(v___x_6156_, 1);
                        v___x_6158_ = l_Lean_Core_instantiateValueLevelParams(
                            v_a_6157_,
                            v_us_6143_,
                            v___x_6155_,
                            v_a_6151_,
                            v_a_6152_,
                        );
                        leanh::lean_dec(v_a_6157_);
                        if leanh::lean_obj_tag(v___x_6158_) == 0 {
                            v_a_6159_ = leanh::lean_ctor_get(v___x_6158_, 0);
                            leanh::lean_inc(v_a_6159_);
                            leanh::lean_dec_ref_known(v___x_6158_, 1);
                            v___x_6160_ = l_Lean_Expr_beta(v_a_6159_, v_args_6147_);
                            v___x_6161_ = 1;
                            v___x_6162_ = 1;
                            v___x_6163_ = l_Lean_Meta_mkLetFVars(
                                v_letFVars_6148_,
                                v___x_6160_,
                                v___x_6161_,
                                v___x_6161_,
                                v___x_6162_,
                                v_a_6149_,
                                v_a_6150_,
                                v_a_6151_,
                                v_a_6152_,
                            );
                            leanh::lean_dec_ref(v_letFVars_6148_);
                            return v___x_6163_;
                        } else {
                            leanh::lean_dec_ref(v_letFVars_6148_);
                            leanh::lean_dec_ref(v_args_6147_);
                            return v___x_6158_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_letFVars_6148_);
                        leanh::lean_dec_ref(v_args_6147_);
                        leanh::lean_dec(v_us_6143_);
                        v_a_6164_ = leanh::lean_ctor_get(v___x_6156_, 0);
                        v_isSharedCheck_6171_ =
                            (!leanh::lean_is_exclusive(v___x_6156_)) as u8;
                        if v_isSharedCheck_6171_ == 0 {
                            v___x_6166_ = v___x_6156_;
                            v_isShared_6167_ = v_isSharedCheck_6171_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6164_);
                            leanh::lean_dec(v___x_6156_);
                            v___x_6166_ = leanh::lean_box(0);
                            v_isShared_6167_ = v_isSharedCheck_6171_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_6172_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_6144_);
                    v_altIdx_6173_ = lean_nat_add(v_i_6146_, v___x_6172_);
                    leanh::lean_dec(v___x_6172_);
                    v_numParams_6174_ = lean_array_fget_borrowed(v_altNumParams_6145_, v_i_6146_);
                    v___x_6175_ = l_Lean_instInhabitedExpr;
                    v___x_6176_ =
                        lean_array_get_borrowed(v___x_6175_, v_args_6147_, v_altIdx_6173_);
                    leanh::lean_inc(v_numParams_6174_);
                    leanh::lean_inc(v___x_6176_);
                    v___x_6177_ =
                        l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(
                            v___x_6176_,
                            v_numParams_6174_,
                            v_a_6149_,
                            v_a_6150_,
                            v_a_6151_,
                            v_a_6152_,
                        );
                    if leanh::lean_obj_tag(v___x_6177_) == 0 {
                        v_a_6178_ = leanh::lean_ctor_get(v___x_6177_, 0);
                        leanh::lean_inc(v_a_6178_);
                        leanh::lean_dec_ref_known(v___x_6177_, 1);
                        v___x_6179_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
                        v___x_6180_ =
                            l_Lean_Core_mkFreshUserName(v___x_6179_, v_a_6151_, v_a_6152_);
                        if leanh::lean_obj_tag(v___x_6180_) == 0 {
                            v_a_6181_ = leanh::lean_ctor_get(v___x_6180_, 0);
                            leanh::lean_inc(v_a_6181_);
                            leanh::lean_dec_ref_known(v___x_6180_, 1);
                            leanh::lean_inc(v_a_6152_);
                            leanh::lean_inc_ref(v_a_6151_);
                            leanh::lean_inc(v_a_6150_);
                            leanh::lean_inc_ref(v_a_6149_);
                            leanh::lean_inc(v_a_6178_);
                            v___x_6182_ = lean_infer_type(
                                v_a_6178_, v_a_6149_, v_a_6150_, v_a_6151_, v_a_6152_,
                            );
                            if leanh::lean_obj_tag(v___x_6182_) == 0 {
                                v_a_6183_ = leanh::lean_ctor_get(v___x_6182_, 0);
                                leanh::lean_inc(v_a_6183_);
                                leanh::lean_dec_ref_known(v___x_6182_, 1);
                                v___f_6184_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed as *mut core::ffi::c_void, 14, 8);
                                leanh::lean_closure_set(v___f_6184_, 0, v_i_6146_);
                                leanh::lean_closure_set(v___f_6184_, 1, v_args_6147_);
                                leanh::lean_closure_set(v___f_6184_, 2, v_altIdx_6173_);
                                leanh::lean_closure_set(v___f_6184_, 3, v_letFVars_6148_);
                                leanh::lean_closure_set(v___f_6184_, 4, v_declName_6142_);
                                leanh::lean_closure_set(v___f_6184_, 5, v_us_6143_);
                                leanh::lean_closure_set(v___f_6184_, 6, v_info_6144_);
                                leanh::lean_closure_set(
                                    v___f_6184_,
                                    7,
                                    v_altNumParams_6145_,
                                );
                                v___x_6185_ = 0;
                                v___x_6186_ = 0;
                                v___x_6187_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(v_a_6181_, v_a_6183_, v_a_6178_, v___f_6184_, v___x_6185_, v___x_6186_, v_a_6149_, v_a_6150_, v_a_6151_, v_a_6152_);
                                return v___x_6187_;
                            } else {
                                leanh::lean_dec(v_a_6181_);
                                leanh::lean_dec(v_a_6178_);
                                leanh::lean_dec(v_altIdx_6173_);
                                leanh::lean_dec_ref(v_letFVars_6148_);
                                leanh::lean_dec_ref(v_args_6147_);
                                leanh::lean_dec(v_i_6146_);
                                leanh::lean_dec_ref(v_altNumParams_6145_);
                                leanh::lean_dec_ref(v_info_6144_);
                                leanh::lean_dec(v_us_6143_);
                                leanh::lean_dec(v_declName_6142_);
                                return v___x_6182_;
                            }
                        } else {
                            leanh::lean_dec(v_a_6178_);
                            leanh::lean_dec(v_altIdx_6173_);
                            leanh::lean_dec_ref(v_letFVars_6148_);
                            leanh::lean_dec_ref(v_args_6147_);
                            leanh::lean_dec(v_i_6146_);
                            leanh::lean_dec_ref(v_altNumParams_6145_);
                            leanh::lean_dec_ref(v_info_6144_);
                            leanh::lean_dec(v_us_6143_);
                            leanh::lean_dec(v_declName_6142_);
                            v_a_6188_ = leanh::lean_ctor_get(v___x_6180_, 0);
                            v_isSharedCheck_6195_ =
                                (!leanh::lean_is_exclusive(v___x_6180_)) as u8;
                            if v_isSharedCheck_6195_ == 0 {
                                v___x_6190_ = v___x_6180_;
                                v_isShared_6191_ = v_isSharedCheck_6195_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6188_);
                                leanh::lean_dec(v___x_6180_);
                                v___x_6190_ = leanh::lean_box(0);
                                v_isShared_6191_ = v_isSharedCheck_6195_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_altIdx_6173_);
                        leanh::lean_dec_ref(v_letFVars_6148_);
                        leanh::lean_dec_ref(v_args_6147_);
                        leanh::lean_dec(v_i_6146_);
                        leanh::lean_dec_ref(v_altNumParams_6145_);
                        leanh::lean_dec_ref(v_info_6144_);
                        leanh::lean_dec(v_us_6143_);
                        leanh::lean_dec(v_declName_6142_);
                        return v___x_6177_;
                    }
                }
            }
            1 => {
                if v_isShared_6167_ == 0 {
                    v___x_6169_ = v___x_6166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6170_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_a_6164_);
                    v___x_6169_ = v_reuseFailAlloc_6170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6169_;
            }
            3 => {
                if v_isShared_6191_ == 0 {
                    v___x_6193_ = v___x_6190_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_a_6188_);
                    v___x_6193_ = v_reuseFailAlloc_6194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(
    mut v_i_6196_: *mut leanh::LeanObject,
    mut v_args_6197_: *mut leanh::LeanObject,
    mut v_altIdx_6198_: *mut leanh::LeanObject,
    mut v_letFVars_6199_: *mut leanh::LeanObject,
    mut v_declName_6200_: *mut leanh::LeanObject,
    mut v_us_6201_: *mut leanh::LeanObject,
    mut v_info_6202_: *mut leanh::LeanObject,
    mut v_altNumParams_6203_: *mut leanh::LeanObject,
    mut v_altFVar_6204_: *mut leanh::LeanObject,
    mut v___y_6205_: *mut leanh::LeanObject,
    mut v___y_6206_: *mut leanh::LeanObject,
    mut v___y_6207_: *mut leanh::LeanObject,
    mut v___y_6208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6210_ = leanh::lean_unsigned_to_nat(1);
    v___x_6211_ = lean_nat_add(v_i_6196_, v___x_6210_);
    leanh::lean_inc_ref(v_altFVar_6204_);
    v___x_6212_ = lean_array_set(v_args_6197_, v_altIdx_6198_, v_altFVar_6204_);
    v___x_6213_ = lean_array_push(v_letFVars_6199_, v_altFVar_6204_);
    v___x_6214_ =
        l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(
            v_declName_6200_,
            v_us_6201_,
            v_info_6202_,
            v_altNumParams_6203_,
            v___x_6211_,
            v___x_6212_,
            v___x_6213_,
            v___y_6205_,
            v___y_6206_,
            v___y_6207_,
            v___y_6208_,
        );
    return v___x_6214_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___boxed(
    mut v_declName_6215_: *mut leanh::LeanObject,
    mut v_us_6216_: *mut leanh::LeanObject,
    mut v_info_6217_: *mut leanh::LeanObject,
    mut v_altNumParams_6218_: *mut leanh::LeanObject,
    mut v_i_6219_: *mut leanh::LeanObject,
    mut v_args_6220_: *mut leanh::LeanObject,
    mut v_letFVars_6221_: *mut leanh::LeanObject,
    mut v_a_6222_: *mut leanh::LeanObject,
    mut v_a_6223_: *mut leanh::LeanObject,
    mut v_a_6224_: *mut leanh::LeanObject,
    mut v_a_6225_: *mut leanh::LeanObject,
    mut v_a_6226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6227_ =
        l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(
            v_declName_6215_,
            v_us_6216_,
            v_info_6217_,
            v_altNumParams_6218_,
            v_i_6219_,
            v_args_6220_,
            v_letFVars_6221_,
            v_a_6222_,
            v_a_6223_,
            v_a_6224_,
            v_a_6225_,
        );
    leanh::lean_dec(v_a_6225_);
    leanh::lean_dec_ref(v_a_6224_);
    leanh::lean_dec(v_a_6223_);
    leanh::lean_dec_ref(v_a_6222_);
    return v_res_6227_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0(
    mut v_00_u03b1_6228_: *mut leanh::LeanObject,
    mut v_constName_6229_: *mut leanh::LeanObject,
    mut v___y_6230_: *mut leanh::LeanObject,
    mut v___y_6231_: *mut leanh::LeanObject,
    mut v___y_6232_: *mut leanh::LeanObject,
    mut v___y_6233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6235_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0___redArg(v_constName_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
    return v___x_6235_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0___boxed(
    mut v_00_u03b1_6236_: *mut leanh::LeanObject,
    mut v_constName_6237_: *mut leanh::LeanObject,
    mut v___y_6238_: *mut leanh::LeanObject,
    mut v___y_6239_: *mut leanh::LeanObject,
    mut v___y_6240_: *mut leanh::LeanObject,
    mut v___y_6241_: *mut leanh::LeanObject,
    mut v___y_6242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6243_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0(v_00_u03b1_6236_, v_constName_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
    leanh::lean_dec(v___y_6241_);
    leanh::lean_dec_ref(v___y_6240_);
    leanh::lean_dec(v___y_6239_);
    leanh::lean_dec_ref(v___y_6238_);
    return v_res_6243_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1(
    mut v_00_u03b1_6244_: *mut leanh::LeanObject,
    mut v_ref_6245_: *mut leanh::LeanObject,
    mut v_constName_6246_: *mut leanh::LeanObject,
    mut v___y_6247_: *mut leanh::LeanObject,
    mut v___y_6248_: *mut leanh::LeanObject,
    mut v___y_6249_: *mut leanh::LeanObject,
    mut v___y_6250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6252_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1___redArg(v_ref_6245_, v_constName_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_);
    return v___x_6252_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_6253_: *mut leanh::LeanObject,
    mut v_ref_6254_: *mut leanh::LeanObject,
    mut v_constName_6255_: *mut leanh::LeanObject,
    mut v___y_6256_: *mut leanh::LeanObject,
    mut v___y_6257_: *mut leanh::LeanObject,
    mut v___y_6258_: *mut leanh::LeanObject,
    mut v___y_6259_: *mut leanh::LeanObject,
    mut v___y_6260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6261_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1(v_00_u03b1_6253_, v_ref_6254_, v_constName_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
    leanh::lean_dec(v___y_6259_);
    leanh::lean_dec_ref(v___y_6258_);
    leanh::lean_dec(v___y_6257_);
    leanh::lean_dec_ref(v___y_6256_);
    leanh::lean_dec(v_ref_6254_);
    return v_res_6261_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_6262_: *mut leanh::LeanObject,
    mut v_ref_6263_: *mut leanh::LeanObject,
    mut v_msg_6264_: *mut leanh::LeanObject,
    mut v_declHint_6265_: *mut leanh::LeanObject,
    mut v___y_6266_: *mut leanh::LeanObject,
    mut v___y_6267_: *mut leanh::LeanObject,
    mut v___y_6268_: *mut leanh::LeanObject,
    mut v___y_6269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6271_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_6263_, v_msg_6264_, v_declHint_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_);
    return v___x_6271_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_6272_: *mut leanh::LeanObject,
    mut v_ref_6273_: *mut leanh::LeanObject,
    mut v_msg_6274_: *mut leanh::LeanObject,
    mut v_declHint_6275_: *mut leanh::LeanObject,
    mut v___y_6276_: *mut leanh::LeanObject,
    mut v___y_6277_: *mut leanh::LeanObject,
    mut v___y_6278_: *mut leanh::LeanObject,
    mut v___y_6279_: *mut leanh::LeanObject,
    mut v___y_6280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6281_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_6272_, v_ref_6273_, v_msg_6274_, v_declHint_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
    leanh::lean_dec(v___y_6279_);
    leanh::lean_dec_ref(v___y_6278_);
    leanh::lean_dec(v___y_6277_);
    leanh::lean_dec_ref(v___y_6276_);
    leanh::lean_dec(v_ref_6273_);
    return v_res_6281_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_6282_: *mut leanh::LeanObject,
    mut v_declHint_6283_: *mut leanh::LeanObject,
    mut v___y_6284_: *mut leanh::LeanObject,
    mut v___y_6285_: *mut leanh::LeanObject,
    mut v___y_6286_: *mut leanh::LeanObject,
    mut v___y_6287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6289_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_6282_, v_declHint_6283_, v___y_6287_);
    return v___x_6289_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_6290_: *mut leanh::LeanObject,
    mut v_declHint_6291_: *mut leanh::LeanObject,
    mut v___y_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
    mut v___y_6294_: *mut leanh::LeanObject,
    mut v___y_6295_: *mut leanh::LeanObject,
    mut v___y_6296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6297_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_6290_, v_declHint_6291_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
    leanh::lean_dec(v___y_6295_);
    leanh::lean_dec_ref(v___y_6294_);
    leanh::lean_dec(v___y_6293_);
    leanh::lean_dec_ref(v___y_6292_);
    return v_res_6297_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_6298_: *mut leanh::LeanObject,
    mut v_ref_6299_: *mut leanh::LeanObject,
    mut v_msg_6300_: *mut leanh::LeanObject,
    mut v___y_6301_: *mut leanh::LeanObject,
    mut v___y_6302_: *mut leanh::LeanObject,
    mut v___y_6303_: *mut leanh::LeanObject,
    mut v___y_6304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6306_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_6299_, v_msg_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
    return v___x_6306_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_6307_: *mut leanh::LeanObject,
    mut v_ref_6308_: *mut leanh::LeanObject,
    mut v_msg_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
    mut v___y_6311_: *mut leanh::LeanObject,
    mut v___y_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6315_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_6307_, v_ref_6308_, v_msg_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
    leanh::lean_dec(v___y_6313_);
    leanh::lean_dec_ref(v___y_6312_);
    leanh::lean_dec(v___y_6311_);
    leanh::lean_dec_ref(v___y_6310_);
    leanh::lean_dec(v_ref_6308_);
    return v_res_6315_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_6316_: *mut leanh::LeanObject,
    mut v_msg_6317_: *mut leanh::LeanObject,
    mut v___y_6318_: *mut leanh::LeanObject,
    mut v___y_6319_: *mut leanh::LeanObject,
    mut v___y_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_);
    return v___x_6323_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_6324_: *mut leanh::LeanObject,
    mut v_msg_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
    mut v___y_6327_: *mut leanh::LeanObject,
    mut v___y_6328_: *mut leanh::LeanObject,
    mut v___y_6329_: *mut leanh::LeanObject,
    mut v___y_6330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6331_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_6324_, v_msg_6325_, v___y_6326_, v___y_6327_, v___y_6328_, v___y_6329_);
    leanh::lean_dec(v___y_6329_);
    leanh::lean_dec_ref(v___y_6328_);
    leanh::lean_dec(v___y_6327_);
    leanh::lean_dec_ref(v___y_6326_);
    return v_res_6331_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0___redArg(
    mut v_declName_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6335_ = lean_st_ref_get(v___y_6333_);
    v_env_6336_ = leanh::lean_ctor_get(v___x_6335_, 0);
    leanh::lean_inc_ref(v_env_6336_);
    leanh::lean_dec(v___x_6335_);
    v___x_6337_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6336_, v_declName_6332_);
    v___x_6338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6338_, 0, v___x_6337_);
    return v___x_6338_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0___redArg___boxed(
    mut v_declName_6339_: *mut leanh::LeanObject,
    mut v___y_6340_: *mut leanh::LeanObject,
    mut v___y_6341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6342_ =
        l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0___redArg(
            v_declName_6339_,
            v___y_6340_,
        );
    leanh::lean_dec(v___y_6340_);
    return v_res_6342_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0(
    mut v_declName_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
    mut v___y_6346_: *mut leanh::LeanObject,
    mut v___y_6347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6349_ =
        l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0___redArg(
            v_declName_6343_,
            v___y_6347_,
        );
    return v___x_6349_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0___boxed(
    mut v_declName_6350_: *mut leanh::LeanObject,
    mut v___y_6351_: *mut leanh::LeanObject,
    mut v___y_6352_: *mut leanh::LeanObject,
    mut v___y_6353_: *mut leanh::LeanObject,
    mut v___y_6354_: *mut leanh::LeanObject,
    mut v___y_6355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6356_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0(
        v_declName_6350_,
        v___y_6351_,
        v___y_6352_,
        v___y_6353_,
        v___y_6354_,
    );
    leanh::lean_dec(v___y_6354_);
    leanh::lean_dec_ref(v___y_6353_);
    leanh::lean_dec(v___y_6352_);
    leanh::lean_dec_ref(v___y_6351_);
    return v_res_6356_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1___redArg(
    mut v_declName_6357_: *mut leanh::LeanObject,
    mut v___y_6358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: u8 = 0;
    let mut v___x_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = lean_st_ref_get(v___y_6358_);
    v_env_6361_ = leanh::lean_ctor_get(v___x_6360_, 0);
    leanh::lean_inc_ref(v_env_6361_);
    leanh::lean_dec(v___x_6360_);
    v___x_6362_ = l_Lean_Meta_isMatcherLikeCore(v_env_6361_, v_declName_6357_);
    v___x_6363_ = leanh::lean_box((v___x_6362_) as usize);
    v___x_6364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6364_, 0, v___x_6363_);
    return v___x_6364_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1___redArg___boxed(
    mut v_declName_6365_: *mut leanh::LeanObject,
    mut v___y_6366_: *mut leanh::LeanObject,
    mut v___y_6367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6368_ =
        l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1___redArg(
            v_declName_6365_,
            v___y_6366_,
        );
    leanh::lean_dec(v___y_6366_);
    return v_res_6368_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1(
    mut v_declName_6369_: *mut leanh::LeanObject,
    mut v___y_6370_: *mut leanh::LeanObject,
    mut v___y_6371_: *mut leanh::LeanObject,
    mut v___y_6372_: *mut leanh::LeanObject,
    mut v___y_6373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6375_ =
        l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1___redArg(
            v_declName_6369_,
            v___y_6373_,
        );
    return v___x_6375_;
}
pub unsafe fn l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1___boxed(
    mut v_declName_6376_: *mut leanh::LeanObject,
    mut v___y_6377_: *mut leanh::LeanObject,
    mut v___y_6378_: *mut leanh::LeanObject,
    mut v___y_6379_: *mut leanh::LeanObject,
    mut v___y_6380_: *mut leanh::LeanObject,
    mut v___y_6381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6382_ = l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1(
        v_declName_6376_,
        v___y_6377_,
        v___y_6378_,
        v___y_6379_,
        v___y_6380_,
    );
    leanh::lean_dec(v___y_6380_);
    leanh::lean_dec_ref(v___y_6379_);
    leanh::lean_dec(v___y_6378_);
    leanh::lean_dec_ref(v___y_6377_);
    return v_res_6382_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___lam__0(
    mut v_e_6383_: *mut leanh::LeanObject,
    mut v___y_6384_: *mut leanh::LeanObject,
    mut v___y_6385_: *mut leanh::LeanObject,
    mut v___y_6386_: *mut leanh::LeanObject,
    mut v___y_6387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6389_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6389_, 0, v_e_6383_);
    v___x_6390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6390_, 0, v___x_6389_);
    return v___x_6390_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed(
    mut v_e_6391_: *mut leanh::LeanObject,
    mut v___y_6392_: *mut leanh::LeanObject,
    mut v___y_6393_: *mut leanh::LeanObject,
    mut v___y_6394_: *mut leanh::LeanObject,
    mut v___y_6395_: *mut leanh::LeanObject,
    mut v___y_6396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6397_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__0(
        v_e_6391_,
        v___y_6392_,
        v___y_6393_,
        v___y_6394_,
        v___y_6395_,
    );
    leanh::lean_dec(v___y_6395_);
    leanh::lean_dec_ref(v___y_6394_);
    leanh::lean_dec(v___y_6393_);
    leanh::lean_dec_ref(v___y_6392_);
    return v_res_6397_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___lam__1(
    mut v_e_6398_: *mut leanh::LeanObject,
    mut v___x_6399_: u8,
    mut v___x_6400_: u8,
    mut v_xs_6401_: *mut leanh::LeanObject,
    mut v_x_6402_: *mut leanh::LeanObject,
    mut v___y_6403_: *mut leanh::LeanObject,
    mut v___y_6404_: *mut leanh::LeanObject,
    mut v___y_6405_: *mut leanh::LeanObject,
    mut v___y_6406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: u8 = 0;
    let mut v___x_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6419_: u8 = 0;
    let mut v_a_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6423_: u8 = 0;
    let mut v___x_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6408_ = l_Lean_mkAppN(v_e_6398_, v_xs_6401_);
                v___x_6409_ = 1;
                v___x_6410_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_6401_,
                    v___x_6408_,
                    v___x_6399_,
                    v___x_6400_,
                    v___x_6399_,
                    v___x_6400_,
                    v___x_6409_,
                    v___y_6403_,
                    v___y_6404_,
                    v___y_6405_,
                    v___y_6406_,
                );
                if leanh::lean_obj_tag(v___x_6410_) == 0 {
                    v_a_6411_ = leanh::lean_ctor_get(v___x_6410_, 0);
                    v_isSharedCheck_6419_ = (!leanh::lean_is_exclusive(v___x_6410_)) as u8;
                    if v_isSharedCheck_6419_ == 0 {
                        v___x_6413_ = v___x_6410_;
                        v_isShared_6414_ = v_isSharedCheck_6419_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6411_);
                        leanh::lean_dec(v___x_6410_);
                        v___x_6413_ = leanh::lean_box(0);
                        v_isShared_6414_ = v_isSharedCheck_6419_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6420_ = leanh::lean_ctor_get(v___x_6410_, 0);
                    v_isSharedCheck_6427_ = (!leanh::lean_is_exclusive(v___x_6410_)) as u8;
                    if v_isSharedCheck_6427_ == 0 {
                        v___x_6422_ = v___x_6410_;
                        v_isShared_6423_ = v_isSharedCheck_6427_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6420_);
                        leanh::lean_dec(v___x_6410_);
                        v___x_6422_ = leanh::lean_box(0);
                        v_isShared_6423_ = v_isSharedCheck_6427_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6415_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6415_, 0, v_a_6411_);
                if v_isShared_6414_ == 0 {
                    leanh::lean_ctor_set(v___x_6413_, 0, v___x_6415_);
                    v___x_6417_ = v___x_6413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6418_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6418_, 0, v___x_6415_);
                    v___x_6417_ = v_reuseFailAlloc_6418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6417_;
            }
            3 => {
                if v_isShared_6423_ == 0 {
                    v___x_6425_ = v___x_6422_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6426_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6426_, 0, v_a_6420_);
                    v___x_6425_ = v_reuseFailAlloc_6426_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed(
    mut v_e_6428_: *mut leanh::LeanObject,
    mut v___x_6429_: *mut leanh::LeanObject,
    mut v___x_6430_: *mut leanh::LeanObject,
    mut v_xs_6431_: *mut leanh::LeanObject,
    mut v_x_6432_: *mut leanh::LeanObject,
    mut v___y_6433_: *mut leanh::LeanObject,
    mut v___y_6434_: *mut leanh::LeanObject,
    mut v___y_6435_: *mut leanh::LeanObject,
    mut v___y_6436_: *mut leanh::LeanObject,
    mut v___y_6437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10443__boxed_6438_: u8 = 0;
    let mut v___x_10444__boxed_6439_: u8 = 0;
    let mut v_res_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10443__boxed_6438_ = (leanh::lean_unbox(v___x_6429_) as u8);
    v___x_10444__boxed_6439_ = (leanh::lean_unbox(v___x_6430_) as u8);
    v_res_6440_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__1(
        v_e_6428_,
        v___x_10443__boxed_6438_,
        v___x_10444__boxed_6439_,
        v_xs_6431_,
        v_x_6432_,
        v___y_6433_,
        v___y_6434_,
        v___y_6435_,
        v___y_6436_,
    );
    leanh::lean_dec(v___y_6436_);
    leanh::lean_dec_ref(v___y_6435_);
    leanh::lean_dec(v___y_6434_);
    leanh::lean_dec_ref(v___y_6433_);
    leanh::lean_dec_ref(v_x_6432_);
    leanh::lean_dec_ref(v_xs_6431_);
    return v_res_6440_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___lam__2(
    mut v_e_6443_: *mut leanh::LeanObject,
    mut v___y_6444_: *mut leanh::LeanObject,
    mut v___y_6445_: *mut leanh::LeanObject,
    mut v___y_6446_: *mut leanh::LeanObject,
    mut v___y_6447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v_val_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: u8 = 0;
    let mut v___x_6464_: u8 = 0;
    let mut v_dummy_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6477_: u8 = 0;
    let mut v___x_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6482_: u8 = 0;
    let mut v_a_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6486_: u8 = 0;
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6490_: u8 = 0;
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6504_: u8 = 0;
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6508_: u8 = 0;
    let mut v___x_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6513_: u8 = 0;
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6518_: u8 = 0;
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6531_: u8 = 0;
    let mut v_dummy_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6543_: u8 = 0;
    let mut v_a_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6547_: u8 = 0;
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6551_: u8 = 0;
    let mut v_a_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6555_: u8 = 0;
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6559_: u8 = 0;
    let mut v_isSharedCheck_6560_: u8 = 0;
    let mut v_isSharedCheck_6561_: u8 = 0;
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6449_ = l_Lean_Expr_getAppFn(v_e_6443_);
                if leanh::lean_obj_tag(v___x_6449_) == 4 {
                    v_declName_6450_ = leanh::lean_ctor_get(v___x_6449_, 0);
                    leanh::lean_inc_n(v_declName_6450_, 2);
                    v_us_6451_ = leanh::lean_ctor_get(v___x_6449_, 1);
                    leanh::lean_inc(v_us_6451_);
                    leanh::lean_dec_ref_known(v___x_6449_, 2);
                    v___x_6452_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Compiler_LCNF_inlineMatchers_spec__0___redArg(v_declName_6450_, v___y_6447_);
                    v_a_6453_ = leanh::lean_ctor_get(v___x_6452_, 0);
                    v_isSharedCheck_6561_ = (!leanh::lean_is_exclusive(v___x_6452_)) as u8;
                    if v_isSharedCheck_6561_ == 0 {
                        v___x_6455_ = v___x_6452_;
                        v_isShared_6456_ = v_isSharedCheck_6561_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6453_);
                        leanh::lean_dec(v___x_6452_);
                        v___x_6455_ = leanh::lean_box(0);
                        v_isShared_6456_ = v_isSharedCheck_6561_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6449_);
                    leanh::lean_dec_ref(v_e_6443_);
                    v___x_6562_ = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
                    v___x_6563_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6563_, 0, v___x_6562_);
                    return v___x_6563_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6453_) == 1 {
                    v_val_6457_ = leanh::lean_ctor_get(v_a_6453_, 0);
                    v_isSharedCheck_6513_ = (!leanh::lean_is_exclusive(v_a_6453_)) as u8;
                    if v_isSharedCheck_6513_ == 0 {
                        v___x_6459_ = v_a_6453_;
                        v_isShared_6460_ = v_isSharedCheck_6513_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6457_);
                        leanh::lean_dec(v_a_6453_);
                        v___x_6459_ = leanh::lean_box(0);
                        v_isShared_6460_ = v_isSharedCheck_6513_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6455_);
                    leanh::lean_dec(v_a_6453_);
                    leanh::lean_inc(v_declName_6450_);
                    v___x_6514_ = l_Lean_Meta_isMatcherLike___at___00Lean_Compiler_LCNF_inlineMatchers_spec__1___redArg(v_declName_6450_, v___y_6447_);
                    v_a_6515_ = leanh::lean_ctor_get(v___x_6514_, 0);
                    v_isSharedCheck_6560_ = (!leanh::lean_is_exclusive(v___x_6514_)) as u8;
                    if v_isSharedCheck_6560_ == 0 {
                        v___x_6517_ = v___x_6514_;
                        v_isShared_6518_ = v_isSharedCheck_6560_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6515_);
                        leanh::lean_dec(v___x_6514_);
                        v___x_6517_ = leanh::lean_box(0);
                        v_isShared_6518_ = v_isSharedCheck_6560_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6461_ = l_Lean_Expr_getAppNumArgs(v_e_6443_);
                v___x_6462_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_6457_);
                v___x_6463_ = lean_nat_dec_lt(v___x_6462_, v___x_6461_);
                if v___x_6463_ == 0 {
                    leanh::lean_del_object(v___x_6455_);
                    v___x_6464_ = lean_nat_dec_lt(v___x_6461_, v___x_6462_);
                    if v___x_6464_ == 0 {
                        leanh::lean_dec(v___x_6462_);
                        leanh::lean_del_object(v___x_6459_);
                        v_dummy_6465_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1_once
                            ),
                            _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1,
                        );
                        leanh::lean_inc(v___x_6461_);
                        v___x_6466_ = lean_mk_array(v___x_6461_, v_dummy_6465_);
                        v___x_6467_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6468_ = lean_nat_sub(v___x_6461_, v___x_6467_);
                        leanh::lean_dec(v___x_6461_);
                        v___x_6469_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_e_6443_,
                            v___x_6466_,
                            v___x_6468_,
                        );
                        leanh::lean_inc(v_val_6457_);
                        v___x_6470_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_val_6457_);
                        v___x_6471_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6472_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
                        v___x_6473_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(v_declName_6450_, v_us_6451_, v_val_6457_, v___x_6470_, v___x_6471_, v___x_6469_, v___x_6472_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
                        if leanh::lean_obj_tag(v___x_6473_) == 0 {
                            v_a_6474_ = leanh::lean_ctor_get(v___x_6473_, 0);
                            v_isSharedCheck_6482_ =
                                (!leanh::lean_is_exclusive(v___x_6473_)) as u8;
                            if v_isSharedCheck_6482_ == 0 {
                                v___x_6476_ = v___x_6473_;
                                v_isShared_6477_ = v_isSharedCheck_6482_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6474_);
                                leanh::lean_dec(v___x_6473_);
                                v___x_6476_ = leanh::lean_box(0);
                                v_isShared_6477_ = v_isSharedCheck_6482_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_6483_ = leanh::lean_ctor_get(v___x_6473_, 0);
                            v_isSharedCheck_6490_ =
                                (!leanh::lean_is_exclusive(v___x_6473_)) as u8;
                            if v_isSharedCheck_6490_ == 0 {
                                v___x_6485_ = v___x_6473_;
                                v_isShared_6486_ = v_isSharedCheck_6490_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6483_);
                                leanh::lean_dec(v___x_6473_);
                                v___x_6485_ = leanh::lean_box(0);
                                v_isShared_6486_ = v_isSharedCheck_6490_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_6457_);
                        leanh::lean_dec(v_us_6451_);
                        leanh::lean_dec(v_declName_6450_);
                        leanh::lean_inc(v___y_6447_);
                        leanh::lean_inc_ref(v___y_6446_);
                        leanh::lean_inc(v___y_6445_);
                        leanh::lean_inc_ref(v___y_6444_);
                        leanh::lean_inc_ref(v_e_6443_);
                        v___x_6491_ = lean_infer_type(
                            v_e_6443_,
                            v___y_6444_,
                            v___y_6445_,
                            v___y_6446_,
                            v___y_6447_,
                        );
                        if leanh::lean_obj_tag(v___x_6491_) == 0 {
                            v_a_6492_ = leanh::lean_ctor_get(v___x_6491_, 0);
                            leanh::lean_inc(v_a_6492_);
                            leanh::lean_dec_ref_known(v___x_6491_, 1);
                            v___x_6493_ = leanh::lean_box((v___x_6463_) as usize);
                            v___x_6494_ = leanh::lean_box((v___x_6464_) as usize);
                            v___f_6495_ = leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                3,
                            );
                            leanh::lean_closure_set(v___f_6495_, 0, v_e_6443_);
                            leanh::lean_closure_set(v___f_6495_, 1, v___x_6493_);
                            leanh::lean_closure_set(v___f_6495_, 2, v___x_6494_);
                            v___x_6496_ = lean_nat_sub(v___x_6462_, v___x_6461_);
                            leanh::lean_dec(v___x_6461_);
                            leanh::lean_dec(v___x_6462_);
                            if v_isShared_6460_ == 0 {
                                leanh::lean_ctor_set(v___x_6459_, 0, v___x_6496_);
                                v___x_6498_ = v___x_6459_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_6500_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 0, v___x_6496_);
                                v___x_6498_ = v_reuseFailAlloc_6500_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_6462_);
                            leanh::lean_dec(v___x_6461_);
                            leanh::lean_del_object(v___x_6459_);
                            leanh::lean_dec_ref(v_e_6443_);
                            v_a_6501_ = leanh::lean_ctor_get(v___x_6491_, 0);
                            v_isSharedCheck_6508_ =
                                (!leanh::lean_is_exclusive(v___x_6491_)) as u8;
                            if v_isSharedCheck_6508_ == 0 {
                                v___x_6503_ = v___x_6491_;
                                v_isShared_6504_ = v_isSharedCheck_6508_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6501_);
                                leanh::lean_dec(v___x_6491_);
                                v___x_6503_ = leanh::lean_box(0);
                                v_isShared_6504_ = v_isSharedCheck_6508_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_6462_);
                    leanh::lean_dec(v___x_6461_);
                    leanh::lean_del_object(v___x_6459_);
                    leanh::lean_dec(v_val_6457_);
                    leanh::lean_dec(v_us_6451_);
                    leanh::lean_dec(v_declName_6450_);
                    leanh::lean_dec_ref(v_e_6443_);
                    v___x_6509_ = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
                    if v_isShared_6456_ == 0 {
                        leanh::lean_ctor_set(v___x_6455_, 0, v___x_6509_);
                        v___x_6511_ = v___x_6455_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6512_, 0, v___x_6509_);
                        v___x_6511_ = v_reuseFailAlloc_6512_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6478_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6478_, 0, v_a_6474_);
                if v_isShared_6477_ == 0 {
                    leanh::lean_ctor_set(v___x_6476_, 0, v___x_6478_);
                    v___x_6480_ = v___x_6476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 0, v___x_6478_);
                    v___x_6480_ = v_reuseFailAlloc_6481_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6480_;
            }
            5 => {
                if v_isShared_6486_ == 0 {
                    v___x_6488_ = v___x_6485_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 0, v_a_6483_);
                    v___x_6488_ = v_reuseFailAlloc_6489_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6488_;
            }
            7 => {
                v___x_6499_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(v_a_6492_, v___x_6498_, v___f_6495_, v___x_6463_, v___x_6463_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
                return v___x_6499_;
            }
            8 => {
                if v_isShared_6504_ == 0 {
                    v___x_6506_ = v___x_6503_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_a_6501_);
                    v___x_6506_ = v_reuseFailAlloc_6507_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6506_;
            }
            10 => {
                return v___x_6511_;
            }
            11 => {
                v___x_6519_ = (leanh::lean_unbox(v_a_6515_) as u8);
                leanh::lean_dec(v_a_6515_);
                if v___x_6519_ == 0 {
                    leanh::lean_dec(v_us_6451_);
                    leanh::lean_dec(v_declName_6450_);
                    leanh::lean_dec_ref(v_e_6443_);
                    v___x_6520_ = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
                    if v_isShared_6518_ == 0 {
                        leanh::lean_ctor_set(v___x_6517_, 0, v___x_6520_);
                        v___x_6522_ = v___x_6517_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6523_, 0, v___x_6520_);
                        v___x_6522_ = v_reuseFailAlloc_6523_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6517_);
                    v___x_6524_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_inlineMatchers_inlineMatcher_spec__0(v_declName_6450_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
                    if leanh::lean_obj_tag(v___x_6524_) == 0 {
                        v_a_6525_ = leanh::lean_ctor_get(v___x_6524_, 0);
                        leanh::lean_inc(v_a_6525_);
                        leanh::lean_dec_ref_known(v___x_6524_, 1);
                        v___x_6526_ = 0;
                        v___x_6527_ = l_Lean_Core_instantiateValueLevelParams(
                            v_a_6525_,
                            v_us_6451_,
                            v___x_6526_,
                            v___y_6446_,
                            v___y_6447_,
                        );
                        leanh::lean_dec(v_a_6525_);
                        if leanh::lean_obj_tag(v___x_6527_) == 0 {
                            v_a_6528_ = leanh::lean_ctor_get(v___x_6527_, 0);
                            v_isSharedCheck_6543_ =
                                (!leanh::lean_is_exclusive(v___x_6527_)) as u8;
                            if v_isSharedCheck_6543_ == 0 {
                                v___x_6530_ = v___x_6527_;
                                v_isShared_6531_ = v_isSharedCheck_6543_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6528_);
                                leanh::lean_dec(v___x_6527_);
                                v___x_6530_ = leanh::lean_box(0);
                                v_isShared_6531_ = v_isSharedCheck_6543_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_6443_);
                            v_a_6544_ = leanh::lean_ctor_get(v___x_6527_, 0);
                            v_isSharedCheck_6551_ =
                                (!leanh::lean_is_exclusive(v___x_6527_)) as u8;
                            if v_isSharedCheck_6551_ == 0 {
                                v___x_6546_ = v___x_6527_;
                                v_isShared_6547_ = v_isSharedCheck_6551_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6544_);
                                leanh::lean_dec(v___x_6527_);
                                v___x_6546_ = leanh::lean_box(0);
                                v_isShared_6547_ = v_isSharedCheck_6551_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_us_6451_);
                        leanh::lean_dec_ref(v_e_6443_);
                        v_a_6552_ = leanh::lean_ctor_get(v___x_6524_, 0);
                        v_isSharedCheck_6559_ =
                            (!leanh::lean_is_exclusive(v___x_6524_)) as u8;
                        if v_isSharedCheck_6559_ == 0 {
                            v___x_6554_ = v___x_6524_;
                            v_isShared_6555_ = v_isSharedCheck_6559_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6552_);
                            leanh::lean_dec(v___x_6524_);
                            v___x_6554_ = leanh::lean_box(0);
                            v_isShared_6555_ = v_isSharedCheck_6559_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            12 => {
                return v___x_6522_;
            }
            13 => {
                v_dummy_6532_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1,
                );
                v_nargs_6533_ = l_Lean_Expr_getAppNumArgs(v_e_6443_);
                leanh::lean_inc(v_nargs_6533_);
                v___x_6534_ = lean_mk_array(v_nargs_6533_, v_dummy_6532_);
                v___x_6535_ = leanh::lean_unsigned_to_nat(1);
                v___x_6536_ = lean_nat_sub(v_nargs_6533_, v___x_6535_);
                leanh::lean_dec(v_nargs_6533_);
                v___x_6537_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_6443_,
                    v___x_6534_,
                    v___x_6536_,
                );
                v___x_6538_ = l_Lean_Expr_beta(v_a_6528_, v___x_6537_);
                v___x_6539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6539_, 0, v___x_6538_);
                if v_isShared_6531_ == 0 {
                    leanh::lean_ctor_set(v___x_6530_, 0, v___x_6539_);
                    v___x_6541_ = v___x_6530_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6542_, 0, v___x_6539_);
                    v___x_6541_ = v_reuseFailAlloc_6542_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6541_;
            }
            15 => {
                if v_isShared_6547_ == 0 {
                    v___x_6549_ = v___x_6546_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6550_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6544_);
                    v___x_6549_ = v_reuseFailAlloc_6550_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6549_;
            }
            17 => {
                if v_isShared_6555_ == 0 {
                    v___x_6557_ = v___x_6554_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_a_6552_);
                    v___x_6557_ = v_reuseFailAlloc_6558_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___lam__2___boxed(
    mut v_e_6564_: *mut leanh::LeanObject,
    mut v___y_6565_: *mut leanh::LeanObject,
    mut v___y_6566_: *mut leanh::LeanObject,
    mut v___y_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
    mut v___y_6569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6570_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__2(
        v_e_6564_,
        v___y_6565_,
        v___y_6566_,
        v___y_6567_,
        v___y_6568_,
    );
    leanh::lean_dec(v___y_6568_);
    leanh::lean_dec_ref(v___y_6567_);
    leanh::lean_dec(v___y_6566_);
    leanh::lean_dec_ref(v___y_6565_);
    return v_res_6570_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2___lam__0(
    mut v_00_u03b1_6571_: *mut leanh::LeanObject,
    mut v_x_6572_: *mut leanh::LeanObject,
    mut v___y_6573_: *mut leanh::LeanObject,
    mut v___y_6574_: *mut leanh::LeanObject,
    mut v___y_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6578_ = leanh::lean_apply_1(v_x_6572_, leanh::lean_box(0));
    v___x_6579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6579_, 0, v___x_6578_);
    return v___x_6579_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2___lam__0___boxed(
    mut v_00_u03b1_6580_: *mut leanh::LeanObject,
    mut v_x_6581_: *mut leanh::LeanObject,
    mut v___y_6582_: *mut leanh::LeanObject,
    mut v___y_6583_: *mut leanh::LeanObject,
    mut v___y_6584_: *mut leanh::LeanObject,
    mut v___y_6585_: *mut leanh::LeanObject,
    mut v___y_6586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6587_ = l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2___lam__0(
        v_00_u03b1_6580_,
        v_x_6581_,
        v___y_6582_,
        v___y_6583_,
        v___y_6584_,
        v___y_6585_,
    );
    leanh::lean_dec(v___y_6585_);
    leanh::lean_dec_ref(v___y_6584_);
    leanh::lean_dec(v___y_6583_);
    leanh::lean_dec_ref(v___y_6582_);
    return v_res_6587_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg___lam__0(
    mut v_k_6588_: *mut leanh::LeanObject,
    mut v___y_6589_: *mut leanh::LeanObject,
    mut v_b_6590_: *mut leanh::LeanObject,
    mut v___y_6591_: *mut leanh::LeanObject,
    mut v___y_6592_: *mut leanh::LeanObject,
    mut v___y_6593_: *mut leanh::LeanObject,
    mut v___y_6594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_6594_);
    leanh::lean_inc_ref(v___y_6593_);
    leanh::lean_inc(v___y_6592_);
    leanh::lean_inc_ref(v___y_6591_);
    leanh::lean_inc(v___y_6589_);
    v___x_6596_ = leanh::lean_apply_7(
        v_k_6588_,
        v_b_6590_,
        v___y_6589_,
        v___y_6591_,
        v___y_6592_,
        v___y_6593_,
        v___y_6594_,
        leanh::lean_box(0),
    );
    return v___x_6596_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg___lam__0___boxed(
    mut v_k_6597_: *mut leanh::LeanObject,
    mut v___y_6598_: *mut leanh::LeanObject,
    mut v_b_6599_: *mut leanh::LeanObject,
    mut v___y_6600_: *mut leanh::LeanObject,
    mut v___y_6601_: *mut leanh::LeanObject,
    mut v___y_6602_: *mut leanh::LeanObject,
    mut v___y_6603_: *mut leanh::LeanObject,
    mut v___y_6604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6605_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg___lam__0(v_k_6597_, v___y_6598_, v_b_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_);
    leanh::lean_dec(v___y_6603_);
    leanh::lean_dec_ref(v___y_6602_);
    leanh::lean_dec(v___y_6601_);
    leanh::lean_dec_ref(v___y_6600_);
    leanh::lean_dec(v___y_6598_);
    return v_res_6605_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10___redArg(
    mut v_name_6606_: *mut leanh::LeanObject,
    mut v_type_6607_: *mut leanh::LeanObject,
    mut v_val_6608_: *mut leanh::LeanObject,
    mut v_k_6609_: *mut leanh::LeanObject,
    mut v_nondep_6610_: u8,
    mut v_kind_6611_: u8,
    mut v___y_6612_: *mut leanh::LeanObject,
    mut v___y_6613_: *mut leanh::LeanObject,
    mut v___y_6614_: *mut leanh::LeanObject,
    mut v___y_6615_: *mut leanh::LeanObject,
    mut v___y_6616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6623_: u8 = 0;
    let mut v___x_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_6612_);
                v___f_6618_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                leanh::lean_closure_set(v___f_6618_, 0, v_k_6609_);
                leanh::lean_closure_set(v___f_6618_, 1, v___y_6612_);
                v___x_6619_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_6606_,
                    v_type_6607_,
                    v_val_6608_,
                    v___f_6618_,
                    v_nondep_6610_,
                    v_kind_6611_,
                    v___y_6613_,
                    v___y_6614_,
                    v___y_6615_,
                    v___y_6616_,
                );
                if leanh::lean_obj_tag(v___x_6619_) == 0 {
                    return v___x_6619_;
                } else {
                    v_a_6620_ = leanh::lean_ctor_get(v___x_6619_, 0);
                    v_isSharedCheck_6627_ = (!leanh::lean_is_exclusive(v___x_6619_)) as u8;
                    if v_isSharedCheck_6627_ == 0 {
                        v___x_6622_ = v___x_6619_;
                        v_isShared_6623_ = v_isSharedCheck_6627_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6620_);
                        leanh::lean_dec(v___x_6619_);
                        v___x_6622_ = leanh::lean_box(0);
                        v_isShared_6623_ = v_isSharedCheck_6627_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6623_ == 0 {
                    v___x_6625_ = v___x_6622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_a_6620_);
                    v___x_6625_ = v_reuseFailAlloc_6626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10___redArg___boxed(
    mut v_name_6628_: *mut leanh::LeanObject,
    mut v_type_6629_: *mut leanh::LeanObject,
    mut v_val_6630_: *mut leanh::LeanObject,
    mut v_k_6631_: *mut leanh::LeanObject,
    mut v_nondep_6632_: *mut leanh::LeanObject,
    mut v_kind_6633_: *mut leanh::LeanObject,
    mut v___y_6634_: *mut leanh::LeanObject,
    mut v___y_6635_: *mut leanh::LeanObject,
    mut v___y_6636_: *mut leanh::LeanObject,
    mut v___y_6637_: *mut leanh::LeanObject,
    mut v___y_6638_: *mut leanh::LeanObject,
    mut v___y_6639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_6640_: u8 = 0;
    let mut v_kind_boxed_6641_: u8 = 0;
    let mut v_res_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6640_ = (leanh::lean_unbox(v_nondep_6632_) as u8);
    v_kind_boxed_6641_ = (leanh::lean_unbox(v_kind_6633_) as u8);
    v_res_6642_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10___redArg(v_name_6628_, v_type_6629_, v_val_6630_, v_k_6631_, v_nondep_boxed_6640_, v_kind_boxed_6641_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
    leanh::lean_dec(v___y_6638_);
    leanh::lean_dec_ref(v___y_6637_);
    leanh::lean_dec(v___y_6636_);
    leanh::lean_dec_ref(v___y_6635_);
    leanh::lean_dec(v___y_6634_);
    return v_res_6642_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__2(
    mut v___x_6643_: *mut leanh::LeanObject,
    mut v___y_6644_: *mut leanh::LeanObject,
    mut v___y_6645_: *mut leanh::LeanObject,
    mut v___y_6646_: *mut leanh::LeanObject,
    mut v___y_6647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6649_, 0, v___x_6643_);
    return v___x_6649_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__2___boxed(
    mut v___x_6650_: *mut leanh::LeanObject,
    mut v___y_6651_: *mut leanh::LeanObject,
    mut v___y_6652_: *mut leanh::LeanObject,
    mut v___y_6653_: *mut leanh::LeanObject,
    mut v___y_6654_: *mut leanh::LeanObject,
    mut v___y_6655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__2(v___x_6650_, v___y_6651_, v___y_6652_, v___y_6653_, v___y_6654_);
    leanh::lean_dec(v___y_6654_);
    leanh::lean_dec_ref(v___y_6653_);
    leanh::lean_dec(v___y_6652_);
    leanh::lean_dec_ref(v___y_6651_);
    return v_res_6656_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg(
    mut v_name_6657_: *mut leanh::LeanObject,
    mut v_bi_6658_: u8,
    mut v_type_6659_: *mut leanh::LeanObject,
    mut v_k_6660_: *mut leanh::LeanObject,
    mut v_kind_6661_: u8,
    mut v___y_6662_: *mut leanh::LeanObject,
    mut v___y_6663_: *mut leanh::LeanObject,
    mut v___y_6664_: *mut leanh::LeanObject,
    mut v___y_6665_: *mut leanh::LeanObject,
    mut v___y_6666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6673_: u8 = 0;
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_6662_);
                v___f_6668_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                leanh::lean_closure_set(v___f_6668_, 0, v_k_6660_);
                leanh::lean_closure_set(v___f_6668_, 1, v___y_6662_);
                v___x_6669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_6657_,
                    v_bi_6658_,
                    v_type_6659_,
                    v___f_6668_,
                    v_kind_6661_,
                    v___y_6663_,
                    v___y_6664_,
                    v___y_6665_,
                    v___y_6666_,
                );
                if leanh::lean_obj_tag(v___x_6669_) == 0 {
                    return v___x_6669_;
                } else {
                    v_a_6670_ = leanh::lean_ctor_get(v___x_6669_, 0);
                    v_isSharedCheck_6677_ = (!leanh::lean_is_exclusive(v___x_6669_)) as u8;
                    if v_isSharedCheck_6677_ == 0 {
                        v___x_6672_ = v___x_6669_;
                        v_isShared_6673_ = v_isSharedCheck_6677_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6670_);
                        leanh::lean_dec(v___x_6669_);
                        v___x_6672_ = leanh::lean_box(0);
                        v_isShared_6673_ = v_isSharedCheck_6677_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6673_ == 0 {
                    v___x_6675_ = v___x_6672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6676_, 0, v_a_6670_);
                    v___x_6675_ = v_reuseFailAlloc_6676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg___boxed(
    mut v_name_6678_: *mut leanh::LeanObject,
    mut v_bi_6679_: *mut leanh::LeanObject,
    mut v_type_6680_: *mut leanh::LeanObject,
    mut v_k_6681_: *mut leanh::LeanObject,
    mut v_kind_6682_: *mut leanh::LeanObject,
    mut v___y_6683_: *mut leanh::LeanObject,
    mut v___y_6684_: *mut leanh::LeanObject,
    mut v___y_6685_: *mut leanh::LeanObject,
    mut v___y_6686_: *mut leanh::LeanObject,
    mut v___y_6687_: *mut leanh::LeanObject,
    mut v___y_6688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_6689_: u8 = 0;
    let mut v_kind_boxed_6690_: u8 = 0;
    let mut v_res_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6689_ = (leanh::lean_unbox(v_bi_6679_) as u8);
    v_kind_boxed_6690_ = (leanh::lean_unbox(v_kind_6682_) as u8);
    v_res_6691_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg(v_name_6678_, v_bi_boxed_6689_, v_type_6680_, v_k_6681_, v_kind_boxed_6690_, v___y_6683_, v___y_6684_, v___y_6685_, v___y_6686_, v___y_6687_);
    leanh::lean_dec(v___y_6687_);
    leanh::lean_dec_ref(v___y_6686_);
    leanh::lean_dec(v___y_6685_);
    leanh::lean_dec_ref(v___y_6684_);
    leanh::lean_dec(v___y_6683_);
    return v_res_6691_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13___redArg(
    mut v_ref_6692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6694_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__8_spec__11___redArg___closed__5);
    v___x_6695_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6695_, 0, v_ref_6692_);
    leanh::lean_ctor_set(v___x_6695_, 1, v___x_6694_);
    v___x_6696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6696_, 0, v___x_6695_);
    return v___x_6696_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13___redArg___boxed(
    mut v_ref_6697_: *mut leanh::LeanObject,
    mut v___y_6698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6699_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13___redArg(v_ref_6697_);
    return v_res_6699_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10___redArg(
    mut v_x_6700_: *mut leanh::LeanObject,
    mut v___y_6701_: *mut leanh::LeanObject,
    mut v___y_6702_: *mut leanh::LeanObject,
    mut v___y_6703_: *mut leanh::LeanObject,
    mut v___y_6704_: *mut leanh::LeanObject,
    mut v___y_6705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6712_: u8 = 0;
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6716_: u8 = 0;
    let mut v_fileName_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6729_: u8 = 0;
    let mut v_cancelTk_x3f_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6731_: u8 = 0;
    let mut v_inheritedTraceOptions_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: u8 = 0;
    let mut v___x_6740_: u8 = 0;
    let mut v___x_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6717_ = leanh::lean_ctor_get(v___y_6704_, 0);
                v_fileMap_6718_ = leanh::lean_ctor_get(v___y_6704_, 1);
                v_options_6719_ = leanh::lean_ctor_get(v___y_6704_, 2);
                v_currRecDepth_6720_ = leanh::lean_ctor_get(v___y_6704_, 3);
                v_maxRecDepth_6721_ = leanh::lean_ctor_get(v___y_6704_, 4);
                v_ref_6722_ = leanh::lean_ctor_get(v___y_6704_, 5);
                v_currNamespace_6723_ = leanh::lean_ctor_get(v___y_6704_, 6);
                v_openDecls_6724_ = leanh::lean_ctor_get(v___y_6704_, 7);
                v_initHeartbeats_6725_ = leanh::lean_ctor_get(v___y_6704_, 8);
                v_maxHeartbeats_6726_ = leanh::lean_ctor_get(v___y_6704_, 9);
                v_quotContext_6727_ = leanh::lean_ctor_get(v___y_6704_, 10);
                v_currMacroScope_6728_ = leanh::lean_ctor_get(v___y_6704_, 11);
                v_diag_6729_ = leanh::lean_ctor_get_uint8(
                    v___y_6704_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6730_ = leanh::lean_ctor_get(v___y_6704_, 12);
                v_suppressElabErrors_6731_ = leanh::lean_ctor_get_uint8(
                    v___y_6704_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6732_ = leanh::lean_ctor_get(v___y_6704_, 13);
                v___x_6738_ = leanh::lean_unsigned_to_nat(0);
                v___x_6739_ = lean_nat_dec_eq(v_maxRecDepth_6721_, v___x_6738_);
                if v___x_6739_ == 0 {
                    v___x_6740_ = lean_nat_dec_eq(v_currRecDepth_6720_, v_maxRecDepth_6721_);
                    if v___x_6740_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_6700_);
                        leanh::lean_inc(v_ref_6722_);
                        v___x_6741_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13___redArg(v_ref_6722_);
                        v___y_6708_ = v___x_6741_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_6708_) == 0 {
                    return v___y_6708_;
                } else {
                    v_a_6709_ = leanh::lean_ctor_get(v___y_6708_, 0);
                    v_isSharedCheck_6716_ = (!leanh::lean_is_exclusive(v___y_6708_)) as u8;
                    if v_isSharedCheck_6716_ == 0 {
                        v___x_6711_ = v___y_6708_;
                        v_isShared_6712_ = v_isSharedCheck_6716_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6709_);
                        leanh::lean_dec(v___y_6708_);
                        v___x_6711_ = leanh::lean_box(0);
                        v_isShared_6712_ = v_isSharedCheck_6716_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6712_ == 0 {
                    v___x_6714_ = v___x_6711_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6715_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6715_, 0, v_a_6709_);
                    v___x_6714_ = v_reuseFailAlloc_6715_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6714_;
            }
            4 => {
                v___x_6734_ = leanh::lean_unsigned_to_nat(1);
                v___x_6735_ = lean_nat_add(v_currRecDepth_6720_, v___x_6734_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_6732_);
                leanh::lean_inc(v_cancelTk_x3f_6730_);
                leanh::lean_inc(v_currMacroScope_6728_);
                leanh::lean_inc(v_quotContext_6727_);
                leanh::lean_inc(v_maxHeartbeats_6726_);
                leanh::lean_inc(v_initHeartbeats_6725_);
                leanh::lean_inc(v_openDecls_6724_);
                leanh::lean_inc(v_currNamespace_6723_);
                leanh::lean_inc(v_ref_6722_);
                leanh::lean_inc(v_maxRecDepth_6721_);
                leanh::lean_inc_ref(v_options_6719_);
                leanh::lean_inc_ref(v_fileMap_6718_);
                leanh::lean_inc_ref(v_fileName_6717_);
                v___x_6736_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_6736_, 0, v_fileName_6717_);
                leanh::lean_ctor_set(v___x_6736_, 1, v_fileMap_6718_);
                leanh::lean_ctor_set(v___x_6736_, 2, v_options_6719_);
                leanh::lean_ctor_set(v___x_6736_, 3, v___x_6735_);
                leanh::lean_ctor_set(v___x_6736_, 4, v_maxRecDepth_6721_);
                leanh::lean_ctor_set(v___x_6736_, 5, v_ref_6722_);
                leanh::lean_ctor_set(v___x_6736_, 6, v_currNamespace_6723_);
                leanh::lean_ctor_set(v___x_6736_, 7, v_openDecls_6724_);
                leanh::lean_ctor_set(v___x_6736_, 8, v_initHeartbeats_6725_);
                leanh::lean_ctor_set(v___x_6736_, 9, v_maxHeartbeats_6726_);
                leanh::lean_ctor_set(v___x_6736_, 10, v_quotContext_6727_);
                leanh::lean_ctor_set(v___x_6736_, 11, v_currMacroScope_6728_);
                leanh::lean_ctor_set(v___x_6736_, 12, v_cancelTk_x3f_6730_);
                leanh::lean_ctor_set(v___x_6736_, 13, v_inheritedTraceOptions_6732_);
                leanh::lean_ctor_set_uint8(
                    v___x_6736_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_6729_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6736_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6731_,
                );
                leanh::lean_inc(v___y_6705_);
                leanh::lean_inc(v___y_6703_);
                leanh::lean_inc_ref(v___y_6702_);
                leanh::lean_inc(v___y_6701_);
                v___x_6737_ = leanh::lean_apply_6(
                    v_x_6700_,
                    v___y_6701_,
                    v___y_6702_,
                    v___y_6703_,
                    v___x_6736_,
                    v___y_6705_,
                    leanh::lean_box(0),
                );
                v___y_6708_ = v___x_6737_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10___redArg___boxed(
    mut v_x_6742_: *mut leanh::LeanObject,
    mut v___y_6743_: *mut leanh::LeanObject,
    mut v___y_6744_: *mut leanh::LeanObject,
    mut v___y_6745_: *mut leanh::LeanObject,
    mut v___y_6746_: *mut leanh::LeanObject,
    mut v___y_6747_: *mut leanh::LeanObject,
    mut v___y_6748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6749_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10___redArg(v_x_6742_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_, v___y_6747_);
    leanh::lean_dec(v___y_6747_);
    leanh::lean_dec_ref(v___y_6746_);
    leanh::lean_dec(v___y_6745_);
    leanh::lean_dec_ref(v___y_6744_);
    leanh::lean_dec(v___y_6743_);
    return v_res_6749_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__0(
    mut v_00_u03b1_6750_: *mut leanh::LeanObject,
    mut v_x_6751_: *mut leanh::LeanObject,
    mut v___y_6752_: *mut leanh::LeanObject,
    mut v___y_6753_: *mut leanh::LeanObject,
    mut v___y_6754_: *mut leanh::LeanObject,
    mut v___y_6755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6757_ = leanh::lean_apply_1(v_x_6751_, leanh::lean_box(0));
    v___x_6758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6758_, 0, v___x_6757_);
    return v___x_6758_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__0___boxed(
    mut v_00_u03b1_6759_: *mut leanh::LeanObject,
    mut v_x_6760_: *mut leanh::LeanObject,
    mut v___y_6761_: *mut leanh::LeanObject,
    mut v___y_6762_: *mut leanh::LeanObject,
    mut v___y_6763_: *mut leanh::LeanObject,
    mut v___y_6764_: *mut leanh::LeanObject,
    mut v___y_6765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6766_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__0(v_00_u03b1_6759_, v_x_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_);
    leanh::lean_dec(v___y_6764_);
    leanh::lean_dec_ref(v___y_6763_);
    leanh::lean_dec(v___y_6762_);
    leanh::lean_dec_ref(v___y_6761_);
    return v_res_6766_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7___lam__0(
    mut v_fvars_6767_: *mut leanh::LeanObject,
    mut v_pre_6768_: *mut leanh::LeanObject,
    mut v_post_6769_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6770_: u8,
    mut v_skipConstInApp_6771_: u8,
    mut v_skipInstances_6772_: u8,
    mut v_body_6773_: *mut leanh::LeanObject,
    mut v_x_6774_: *mut leanh::LeanObject,
    mut v___y_6775_: *mut leanh::LeanObject,
    mut v___y_6776_: *mut leanh::LeanObject,
    mut v___y_6777_: *mut leanh::LeanObject,
    mut v___y_6778_: *mut leanh::LeanObject,
    mut v___y_6779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6781_ = lean_array_push(v_fvars_6767_, v_x_6774_);
    v___x_6782_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7(v_pre_6768_, v_post_6769_, v_usedLetOnly_6770_, v_skipConstInApp_6771_, v_skipInstances_6772_, v___x_6781_, v_body_6773_, v___y_6775_, v___y_6776_, v___y_6777_, v___y_6778_, v___y_6779_);
    return v___x_6782_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7___lam__0___boxed(
    mut v_fvars_6783_: *mut leanh::LeanObject,
    mut v_pre_6784_: *mut leanh::LeanObject,
    mut v_post_6785_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6786_: *mut leanh::LeanObject,
    mut v_skipConstInApp_6787_: *mut leanh::LeanObject,
    mut v_skipInstances_6788_: *mut leanh::LeanObject,
    mut v_body_6789_: *mut leanh::LeanObject,
    mut v_x_6790_: *mut leanh::LeanObject,
    mut v___y_6791_: *mut leanh::LeanObject,
    mut v___y_6792_: *mut leanh::LeanObject,
    mut v___y_6793_: *mut leanh::LeanObject,
    mut v___y_6794_: *mut leanh::LeanObject,
    mut v___y_6795_: *mut leanh::LeanObject,
    mut v___y_6796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6797_: u8 = 0;
    let mut v_skipConstInApp_boxed_6798_: u8 = 0;
    let mut v_skipInstances_boxed_6799_: u8 = 0;
    let mut v_res_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6797_ = (leanh::lean_unbox(v_usedLetOnly_6786_) as u8);
    v_skipConstInApp_boxed_6798_ = (leanh::lean_unbox(v_skipConstInApp_6787_) as u8);
    v_skipInstances_boxed_6799_ = (leanh::lean_unbox(v_skipInstances_6788_) as u8);
    v_res_6800_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7___lam__0(v_fvars_6783_, v_pre_6784_, v_post_6785_, v_usedLetOnly_boxed_6797_, v_skipConstInApp_boxed_6798_, v_skipInstances_boxed_6799_, v_body_6789_, v_x_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_);
    leanh::lean_dec(v___y_6795_);
    leanh::lean_dec_ref(v___y_6794_);
    leanh::lean_dec(v___y_6793_);
    leanh::lean_dec_ref(v___y_6792_);
    leanh::lean_dec(v___y_6791_);
    return v_res_6800_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(
    mut v_pre_6801_: *mut leanh::LeanObject,
    mut v_post_6802_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6803_: u8,
    mut v_skipConstInApp_6804_: u8,
    mut v_skipInstances_6805_: u8,
    mut v_e_6806_: *mut leanh::LeanObject,
    mut v_a_6807_: *mut leanh::LeanObject,
    mut v___y_6808_: *mut leanh::LeanObject,
    mut v___y_6809_: *mut leanh::LeanObject,
    mut v___y_6810_: *mut leanh::LeanObject,
    mut v___y_6811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6817_: u8 = 0;
    let mut v_e_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6832_: u8 = 0;
    let mut v_a_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6836_: u8 = 0;
    let mut v___x_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_6802_);
                leanh::lean_inc(v___y_6811_);
                leanh::lean_inc_ref(v___y_6810_);
                leanh::lean_inc(v___y_6809_);
                leanh::lean_inc_ref(v___y_6808_);
                leanh::lean_inc_ref(v_e_6806_);
                v___x_6813_ = leanh::lean_apply_6(
                    v_post_6802_,
                    v_e_6806_,
                    v___y_6808_,
                    v___y_6809_,
                    v___y_6810_,
                    v___y_6811_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6813_) == 0 {
                    v_a_6814_ = leanh::lean_ctor_get(v___x_6813_, 0);
                    v_isSharedCheck_6832_ = (!leanh::lean_is_exclusive(v___x_6813_)) as u8;
                    if v_isSharedCheck_6832_ == 0 {
                        v___x_6816_ = v___x_6813_;
                        v_isShared_6817_ = v_isSharedCheck_6832_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6814_);
                        leanh::lean_dec(v___x_6813_);
                        v___x_6816_ = leanh::lean_box(0);
                        v_isShared_6817_ = v_isSharedCheck_6832_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6806_);
                    leanh::lean_dec_ref(v_post_6802_);
                    leanh::lean_dec_ref(v_pre_6801_);
                    v_a_6833_ = leanh::lean_ctor_get(v___x_6813_, 0);
                    v_isSharedCheck_6840_ = (!leanh::lean_is_exclusive(v___x_6813_)) as u8;
                    if v_isSharedCheck_6840_ == 0 {
                        v___x_6835_ = v___x_6813_;
                        v_isShared_6836_ = v_isSharedCheck_6840_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6833_);
                        leanh::lean_dec(v___x_6813_);
                        v___x_6835_ = leanh::lean_box(0);
                        v_isShared_6836_ = v_isSharedCheck_6840_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_6814_) {
                0 => {
                    leanh::lean_dec_ref(v_e_6806_);
                    leanh::lean_dec_ref(v_post_6802_);
                    leanh::lean_dec_ref(v_pre_6801_);
                    v_e_6818_ = leanh::lean_ctor_get(v_a_6814_, 0);
                    leanh::lean_inc_ref(v_e_6818_);
                    leanh::lean_dec_ref_known(v_a_6814_, 1);
                    if v_isShared_6817_ == 0 {
                        leanh::lean_ctor_set(v___x_6816_, 0, v_e_6818_);
                        v___x_6820_ = v___x_6816_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6821_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_e_6818_);
                        v___x_6820_ = v_reuseFailAlloc_6821_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_6816_);
                    leanh::lean_dec_ref(v_e_6806_);
                    v_e_6822_ = leanh::lean_ctor_get(v_a_6814_, 0);
                    leanh::lean_inc_ref(v_e_6822_);
                    leanh::lean_dec_ref_known(v_a_6814_, 1);
                    v___x_6823_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6801_, v_post_6802_, v_usedLetOnly_6803_, v_skipConstInApp_6804_, v_skipInstances_6805_, v_e_6822_, v_a_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_);
                    return v___x_6823_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_6802_);
                    leanh::lean_dec_ref(v_pre_6801_);
                    v_e_x3f_6824_ = leanh::lean_ctor_get(v_a_6814_, 0);
                    leanh::lean_inc(v_e_x3f_6824_);
                    leanh::lean_dec_ref_known(v_a_6814_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_6824_) == 0 {
                        if v_isShared_6817_ == 0 {
                            leanh::lean_ctor_set(v___x_6816_, 0, v_e_6806_);
                            v___x_6826_ = v___x_6816_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6827_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6827_, 0, v_e_6806_);
                            v___x_6826_ = v_reuseFailAlloc_6827_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6806_);
                        v_val_6828_ = leanh::lean_ctor_get(v_e_x3f_6824_, 0);
                        leanh::lean_inc(v_val_6828_);
                        leanh::lean_dec_ref_known(v_e_x3f_6824_, 1);
                        if v_isShared_6817_ == 0 {
                            leanh::lean_ctor_set(v___x_6816_, 0, v_val_6828_);
                            v___x_6830_ = v___x_6816_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6831_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6831_, 0, v_val_6828_);
                            v___x_6830_ = v_reuseFailAlloc_6831_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_6820_;
            }
            3 => {
                return v___x_6826_;
            }
            4 => {
                return v___x_6830_;
            }
            5 => {
                if v_isShared_6836_ == 0 {
                    v___x_6838_ = v___x_6835_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6839_, 0, v_a_6833_);
                    v___x_6838_ = v_reuseFailAlloc_6839_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7(
    mut v_pre_6841_: *mut leanh::LeanObject,
    mut v_post_6842_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6843_: u8,
    mut v_skipConstInApp_6844_: u8,
    mut v_skipInstances_6845_: u8,
    mut v_fvars_6846_: *mut leanh::LeanObject,
    mut v_e_6847_: *mut leanh::LeanObject,
    mut v_a_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
    mut v___y_6851_: *mut leanh::LeanObject,
    mut v___y_6852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_6847_) == 6 {
        let mut v_binderName_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_6857_: u8 = 0;
        let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_6854_ = leanh::lean_ctor_get(v_e_6847_, 0);
        leanh::lean_inc(v_binderName_6854_);
        v_binderType_6855_ = leanh::lean_ctor_get(v_e_6847_, 1);
        leanh::lean_inc_ref(v_binderType_6855_);
        v_body_6856_ = leanh::lean_ctor_get(v_e_6847_, 2);
        leanh::lean_inc_ref(v_body_6856_);
        v_binderInfo_6857_ = leanh::lean_ctor_get_uint8(
            v_e_6847_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_6847_, 3);
        v___x_6858_ = lean_expr_instantiate_rev(v_binderType_6855_, v_fvars_6846_);
        leanh::lean_dec_ref(v_binderType_6855_);
        leanh::lean_inc_ref(v_post_6842_);
        leanh::lean_inc_ref(v_pre_6841_);
        v___x_6859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6841_, v_post_6842_, v_usedLetOnly_6843_, v_skipConstInApp_6844_, v_skipInstances_6845_, v___x_6858_, v_a_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
        if leanh::lean_obj_tag(v___x_6859_) == 0 {
            let mut v_a_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6865_: u8 = 0;
            let mut v___x_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_6860_ = leanh::lean_ctor_get(v___x_6859_, 0);
            leanh::lean_inc(v_a_6860_);
            leanh::lean_dec_ref_known(v___x_6859_, 1);
            v___x_6861_ = leanh::lean_box((v_usedLetOnly_6843_) as usize);
            v___x_6862_ = leanh::lean_box((v_skipConstInApp_6844_) as usize);
            v___x_6863_ = leanh::lean_box((v_skipInstances_6845_) as usize);
            v___f_6864_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            leanh::lean_closure_set(v___f_6864_, 0, v_fvars_6846_);
            leanh::lean_closure_set(v___f_6864_, 1, v_pre_6841_);
            leanh::lean_closure_set(v___f_6864_, 2, v_post_6842_);
            leanh::lean_closure_set(v___f_6864_, 3, v___x_6861_);
            leanh::lean_closure_set(v___f_6864_, 4, v___x_6862_);
            leanh::lean_closure_set(v___f_6864_, 5, v___x_6863_);
            leanh::lean_closure_set(v___f_6864_, 6, v_body_6856_);
            v___x_6865_ = 0;
            v___x_6866_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg(v_binderName_6854_, v_binderInfo_6857_, v_a_6860_, v___f_6864_, v___x_6865_, v_a_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
            return v___x_6866_;
        } else {
            leanh::lean_dec_ref(v_body_6856_);
            leanh::lean_dec(v_binderName_6854_);
            leanh::lean_dec_ref(v_fvars_6846_);
            leanh::lean_dec_ref(v_post_6842_);
            leanh::lean_dec_ref(v_pre_6841_);
            return v___x_6859_;
        }
    } else {
        let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6867_ = lean_expr_instantiate_rev(v_e_6847_, v_fvars_6846_);
        leanh::lean_dec_ref(v_e_6847_);
        leanh::lean_inc_ref(v_post_6842_);
        leanh::lean_inc_ref(v_pre_6841_);
        v___x_6868_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6841_, v_post_6842_, v_usedLetOnly_6843_, v_skipConstInApp_6844_, v_skipInstances_6845_, v___x_6867_, v_a_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
        if leanh::lean_obj_tag(v___x_6868_) == 0 {
            let mut v_a_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6870_: u8 = 0;
            let mut v___x_6871_: u8 = 0;
            let mut v___x_6872_: u8 = 0;
            let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_6869_ = leanh::lean_ctor_get(v___x_6868_, 0);
            leanh::lean_inc(v_a_6869_);
            leanh::lean_dec_ref_known(v___x_6868_, 1);
            v___x_6870_ = 0;
            v___x_6871_ = 1;
            v___x_6872_ = 1;
            v___x_6873_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_6846_,
                v_a_6869_,
                v___x_6870_,
                v_usedLetOnly_6843_,
                v___x_6870_,
                v___x_6871_,
                v___x_6872_,
                v___y_6849_,
                v___y_6850_,
                v___y_6851_,
                v___y_6852_,
            );
            leanh::lean_dec_ref(v_fvars_6846_);
            if leanh::lean_obj_tag(v___x_6873_) == 0 {
                let mut v_a_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_6874_ = leanh::lean_ctor_get(v___x_6873_, 0);
                leanh::lean_inc(v_a_6874_);
                leanh::lean_dec_ref_known(v___x_6873_, 1);
                v___x_6875_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_6841_, v_post_6842_, v_usedLetOnly_6843_, v_skipConstInApp_6844_, v_skipInstances_6845_, v_a_6874_, v_a_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
                return v___x_6875_;
            } else {
                leanh::lean_dec_ref(v_post_6842_);
                leanh::lean_dec_ref(v_pre_6841_);
                return v___x_6873_;
            }
        } else {
            leanh::lean_dec_ref(v_fvars_6846_);
            leanh::lean_dec_ref(v_post_6842_);
            leanh::lean_dec_ref(v_pre_6841_);
            return v___x_6868_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8___lam__0(
    mut v_fvars_6876_: *mut leanh::LeanObject,
    mut v_pre_6877_: *mut leanh::LeanObject,
    mut v_post_6878_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6879_: u8,
    mut v_skipConstInApp_6880_: u8,
    mut v_skipInstances_6881_: u8,
    mut v_body_6882_: *mut leanh::LeanObject,
    mut v_x_6883_: *mut leanh::LeanObject,
    mut v___y_6884_: *mut leanh::LeanObject,
    mut v___y_6885_: *mut leanh::LeanObject,
    mut v___y_6886_: *mut leanh::LeanObject,
    mut v___y_6887_: *mut leanh::LeanObject,
    mut v___y_6888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6890_ = lean_array_push(v_fvars_6876_, v_x_6883_);
    v___x_6891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8(v_pre_6877_, v_post_6878_, v_usedLetOnly_6879_, v_skipConstInApp_6880_, v_skipInstances_6881_, v___x_6890_, v_body_6882_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_);
    return v___x_6891_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8___lam__0___boxed(
    mut v_fvars_6892_: *mut leanh::LeanObject,
    mut v_pre_6893_: *mut leanh::LeanObject,
    mut v_post_6894_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6895_: *mut leanh::LeanObject,
    mut v_skipConstInApp_6896_: *mut leanh::LeanObject,
    mut v_skipInstances_6897_: *mut leanh::LeanObject,
    mut v_body_6898_: *mut leanh::LeanObject,
    mut v_x_6899_: *mut leanh::LeanObject,
    mut v___y_6900_: *mut leanh::LeanObject,
    mut v___y_6901_: *mut leanh::LeanObject,
    mut v___y_6902_: *mut leanh::LeanObject,
    mut v___y_6903_: *mut leanh::LeanObject,
    mut v___y_6904_: *mut leanh::LeanObject,
    mut v___y_6905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6906_: u8 = 0;
    let mut v_skipConstInApp_boxed_6907_: u8 = 0;
    let mut v_skipInstances_boxed_6908_: u8 = 0;
    let mut v_res_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6906_ = (leanh::lean_unbox(v_usedLetOnly_6895_) as u8);
    v_skipConstInApp_boxed_6907_ = (leanh::lean_unbox(v_skipConstInApp_6896_) as u8);
    v_skipInstances_boxed_6908_ = (leanh::lean_unbox(v_skipInstances_6897_) as u8);
    v_res_6909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8___lam__0(v_fvars_6892_, v_pre_6893_, v_post_6894_, v_usedLetOnly_boxed_6906_, v_skipConstInApp_boxed_6907_, v_skipInstances_boxed_6908_, v_body_6898_, v_x_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_);
    leanh::lean_dec(v___y_6904_);
    leanh::lean_dec_ref(v___y_6903_);
    leanh::lean_dec(v___y_6902_);
    leanh::lean_dec_ref(v___y_6901_);
    leanh::lean_dec(v___y_6900_);
    return v_res_6909_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8(
    mut v_pre_6910_: *mut leanh::LeanObject,
    mut v_post_6911_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6912_: u8,
    mut v_skipConstInApp_6913_: u8,
    mut v_skipInstances_6914_: u8,
    mut v_fvars_6915_: *mut leanh::LeanObject,
    mut v_e_6916_: *mut leanh::LeanObject,
    mut v_a_6917_: *mut leanh::LeanObject,
    mut v___y_6918_: *mut leanh::LeanObject,
    mut v___y_6919_: *mut leanh::LeanObject,
    mut v___y_6920_: *mut leanh::LeanObject,
    mut v___y_6921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_6916_) == 8 {
        let mut v_declName_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_6927_: u8 = 0;
        let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_6923_ = leanh::lean_ctor_get(v_e_6916_, 0);
        leanh::lean_inc(v_declName_6923_);
        v_type_6924_ = leanh::lean_ctor_get(v_e_6916_, 1);
        leanh::lean_inc_ref(v_type_6924_);
        v_value_6925_ = leanh::lean_ctor_get(v_e_6916_, 2);
        leanh::lean_inc_ref(v_value_6925_);
        v_body_6926_ = leanh::lean_ctor_get(v_e_6916_, 3);
        leanh::lean_inc_ref(v_body_6926_);
        v_nondep_6927_ = leanh::lean_ctor_get_uint8(
            v_e_6916_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_6916_, 4);
        v___x_6928_ = lean_expr_instantiate_rev(v_type_6924_, v_fvars_6915_);
        leanh::lean_dec_ref(v_type_6924_);
        leanh::lean_inc_ref(v_post_6911_);
        leanh::lean_inc_ref(v_pre_6910_);
        v___x_6929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6910_, v_post_6911_, v_usedLetOnly_6912_, v_skipConstInApp_6913_, v_skipInstances_6914_, v___x_6928_, v_a_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_);
        if leanh::lean_obj_tag(v___x_6929_) == 0 {
            let mut v_a_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_6930_ = leanh::lean_ctor_get(v___x_6929_, 0);
            leanh::lean_inc(v_a_6930_);
            leanh::lean_dec_ref_known(v___x_6929_, 1);
            v___x_6931_ = lean_expr_instantiate_rev(v_value_6925_, v_fvars_6915_);
            leanh::lean_dec_ref(v_value_6925_);
            leanh::lean_inc_ref(v_post_6911_);
            leanh::lean_inc_ref(v_pre_6910_);
            v___x_6932_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6910_, v_post_6911_, v_usedLetOnly_6912_, v_skipConstInApp_6913_, v_skipInstances_6914_, v___x_6931_, v_a_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_);
            if leanh::lean_obj_tag(v___x_6932_) == 0 {
                let mut v_a_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6938_: u8 = 0;
                let mut v___x_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_6933_ = leanh::lean_ctor_get(v___x_6932_, 0);
                leanh::lean_inc(v_a_6933_);
                leanh::lean_dec_ref_known(v___x_6932_, 1);
                v___x_6934_ = leanh::lean_box((v_usedLetOnly_6912_) as usize);
                v___x_6935_ = leanh::lean_box((v_skipConstInApp_6913_) as usize);
                v___x_6936_ = leanh::lean_box((v_skipInstances_6914_) as usize);
                v___f_6937_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                leanh::lean_closure_set(v___f_6937_, 0, v_fvars_6915_);
                leanh::lean_closure_set(v___f_6937_, 1, v_pre_6910_);
                leanh::lean_closure_set(v___f_6937_, 2, v_post_6911_);
                leanh::lean_closure_set(v___f_6937_, 3, v___x_6934_);
                leanh::lean_closure_set(v___f_6937_, 4, v___x_6935_);
                leanh::lean_closure_set(v___f_6937_, 5, v___x_6936_);
                leanh::lean_closure_set(v___f_6937_, 6, v_body_6926_);
                v___x_6938_ = 0;
                v___x_6939_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10___redArg(v_declName_6923_, v_a_6930_, v_a_6933_, v___f_6937_, v_nondep_6927_, v___x_6938_, v_a_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_);
                return v___x_6939_;
            } else {
                leanh::lean_dec(v_a_6930_);
                leanh::lean_dec_ref(v_body_6926_);
                leanh::lean_dec(v_declName_6923_);
                leanh::lean_dec_ref(v_fvars_6915_);
                leanh::lean_dec_ref(v_post_6911_);
                leanh::lean_dec_ref(v_pre_6910_);
                return v___x_6932_;
            }
        } else {
            leanh::lean_dec_ref(v_body_6926_);
            leanh::lean_dec_ref(v_value_6925_);
            leanh::lean_dec(v_declName_6923_);
            leanh::lean_dec_ref(v_fvars_6915_);
            leanh::lean_dec_ref(v_post_6911_);
            leanh::lean_dec_ref(v_pre_6910_);
            return v___x_6929_;
        }
    } else {
        let mut v___x_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6940_ = lean_expr_instantiate_rev(v_e_6916_, v_fvars_6915_);
        leanh::lean_dec_ref(v_e_6916_);
        leanh::lean_inc_ref(v_post_6911_);
        leanh::lean_inc_ref(v_pre_6910_);
        v___x_6941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6910_, v_post_6911_, v_usedLetOnly_6912_, v_skipConstInApp_6913_, v_skipInstances_6914_, v___x_6940_, v_a_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_);
        if leanh::lean_obj_tag(v___x_6941_) == 0 {
            let mut v_a_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6943_: u8 = 0;
            let mut v___x_6944_: u8 = 0;
            let mut v___x_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_6942_ = leanh::lean_ctor_get(v___x_6941_, 0);
            leanh::lean_inc(v_a_6942_);
            leanh::lean_dec_ref_known(v___x_6941_, 1);
            v___x_6943_ = 0;
            v___x_6944_ = 1;
            v___x_6945_ = l_Lean_Meta_mkLetFVars(
                v_fvars_6915_,
                v_a_6942_,
                v_usedLetOnly_6912_,
                v___x_6943_,
                v___x_6944_,
                v___y_6918_,
                v___y_6919_,
                v___y_6920_,
                v___y_6921_,
            );
            leanh::lean_dec_ref(v_fvars_6915_);
            if leanh::lean_obj_tag(v___x_6945_) == 0 {
                let mut v_a_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_6946_ = leanh::lean_ctor_get(v___x_6945_, 0);
                leanh::lean_inc(v_a_6946_);
                leanh::lean_dec_ref_known(v___x_6945_, 1);
                v___x_6947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_6910_, v_post_6911_, v_usedLetOnly_6912_, v_skipConstInApp_6913_, v_skipInstances_6914_, v_a_6946_, v_a_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_);
                return v___x_6947_;
            } else {
                leanh::lean_dec_ref(v_post_6911_);
                leanh::lean_dec_ref(v_pre_6910_);
                return v___x_6945_;
            }
        } else {
            leanh::lean_dec_ref(v_fvars_6915_);
            leanh::lean_dec_ref(v_post_6911_);
            leanh::lean_dec_ref(v_pre_6910_);
            return v___x_6941_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__3(
    mut v_pre_6948_: *mut leanh::LeanObject,
    mut v_post_6949_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6950_: u8,
    mut v_skipConstInApp_6951_: u8,
    mut v_skipInstances_6952_: u8,
    mut v_sz_6953_: usize,
    mut v_i_6954_: usize,
    mut v_bs_6955_: *mut leanh::LeanObject,
    mut v___y_6956_: *mut leanh::LeanObject,
    mut v___y_6957_: *mut leanh::LeanObject,
    mut v___y_6958_: *mut leanh::LeanObject,
    mut v___y_6959_: *mut leanh::LeanObject,
    mut v___y_6960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6962_: u8 = 0;
    let mut v___x_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: usize = 0;
    let mut v___x_6970_: usize = 0;
    let mut v___x_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6976_: u8 = 0;
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6962_ = lean_usize_dec_lt(v_i_6954_, v_sz_6953_);
                if v___x_6962_ == 0 {
                    leanh::lean_dec_ref(v_post_6949_);
                    leanh::lean_dec_ref(v_pre_6948_);
                    v___x_6963_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6963_, 0, v_bs_6955_);
                    return v___x_6963_;
                } else {
                    v_v_6964_ = lean_array_uget_borrowed(v_bs_6955_, v_i_6954_);
                    leanh::lean_inc(v_v_6964_);
                    leanh::lean_inc_ref(v_post_6949_);
                    leanh::lean_inc_ref(v_pre_6948_);
                    v___x_6965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6948_, v_post_6949_, v_usedLetOnly_6950_, v_skipConstInApp_6951_, v_skipInstances_6952_, v_v_6964_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
                    if leanh::lean_obj_tag(v___x_6965_) == 0 {
                        v_a_6966_ = leanh::lean_ctor_get(v___x_6965_, 0);
                        leanh::lean_inc(v_a_6966_);
                        leanh::lean_dec_ref_known(v___x_6965_, 1);
                        v___x_6967_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6968_ = lean_array_uset(v_bs_6955_, v_i_6954_, v___x_6967_);
                        v___x_6969_ = 1usize;
                        v___x_6970_ = lean_usize_add(v_i_6954_, v___x_6969_);
                        v___x_6971_ = lean_array_uset(v_bs_x27_6968_, v_i_6954_, v_a_6966_);
                        v_i_6954_ = v___x_6970_;
                        v_bs_6955_ = v___x_6971_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_6955_);
                        leanh::lean_dec_ref(v_post_6949_);
                        leanh::lean_dec_ref(v_pre_6948_);
                        v_a_6973_ = leanh::lean_ctor_get(v___x_6965_, 0);
                        v_isSharedCheck_6980_ =
                            (!leanh::lean_is_exclusive(v___x_6965_)) as u8;
                        if v_isSharedCheck_6980_ == 0 {
                            v___x_6975_ = v___x_6965_;
                            v_isShared_6976_ = v_isSharedCheck_6980_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6973_);
                            leanh::lean_dec(v___x_6965_);
                            v___x_6975_ = leanh::lean_box(0);
                            v_isShared_6976_ = v_isSharedCheck_6980_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6976_ == 0 {
                    v___x_6978_ = v___x_6975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6979_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6979_, 0, v_a_6973_);
                    v___x_6978_ = v_reuseFailAlloc_6979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__0(
    mut v_pre_6981_: *mut leanh::LeanObject,
    mut v_post_6982_: *mut leanh::LeanObject,
    mut v_usedLetOnly_6983_: u8,
    mut v_skipConstInApp_6984_: u8,
    mut v_skipInstances_6985_: u8,
    mut v___x_6986_: *mut leanh::LeanObject,
    mut v___y_6987_: *mut leanh::LeanObject,
    mut v_b_6988_: *mut leanh::LeanObject,
    mut v_a_6989_: *mut leanh::LeanObject,
    mut v___y_6990_: *mut leanh::LeanObject,
    mut v___y_6991_: *mut leanh::LeanObject,
    mut v___y_6992_: *mut leanh::LeanObject,
    mut v___y_6993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6999_: u8 = 0;
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7005_: u8 = 0;
    let mut v_a_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7009_: u8 = 0;
    let mut v___x_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_6981_, v_post_6982_, v_usedLetOnly_6983_, v_skipConstInApp_6984_, v_skipInstances_6985_, v___x_6986_, v___y_6987_, v___y_6990_, v___y_6991_, v___y_6992_, v___y_6993_);
                if leanh::lean_obj_tag(v___x_6995_) == 0 {
                    v_a_6996_ = leanh::lean_ctor_get(v___x_6995_, 0);
                    v_isSharedCheck_7005_ = (!leanh::lean_is_exclusive(v___x_6995_)) as u8;
                    if v_isSharedCheck_7005_ == 0 {
                        v___x_6998_ = v___x_6995_;
                        v_isShared_6999_ = v_isSharedCheck_7005_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6996_);
                        leanh::lean_dec(v___x_6995_);
                        v___x_6998_ = leanh::lean_box(0);
                        v_isShared_6999_ = v_isSharedCheck_7005_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_6988_);
                    v_a_7006_ = leanh::lean_ctor_get(v___x_6995_, 0);
                    v_isSharedCheck_7013_ = (!leanh::lean_is_exclusive(v___x_6995_)) as u8;
                    if v_isSharedCheck_7013_ == 0 {
                        v___x_7008_ = v___x_6995_;
                        v_isShared_7009_ = v_isSharedCheck_7013_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7006_);
                        leanh::lean_dec(v___x_6995_);
                        v___x_7008_ = leanh::lean_box(0);
                        v_isShared_7009_ = v_isSharedCheck_7013_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7000_ = lean_array_fset(v_b_6988_, v_a_6989_, v_a_6996_);
                v___x_7001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7001_, 0, v___x_7000_);
                if v_isShared_6999_ == 0 {
                    leanh::lean_ctor_set(v___x_6998_, 0, v___x_7001_);
                    v___x_7003_ = v___x_6998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7004_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7004_, 0, v___x_7001_);
                    v___x_7003_ = v_reuseFailAlloc_7004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7003_;
            }
            3 => {
                if v_isShared_7009_ == 0 {
                    v___x_7011_ = v___x_7008_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7012_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7012_, 0, v_a_7006_);
                    v___x_7011_ = v_reuseFailAlloc_7012_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__0___boxed(
    mut v_pre_7014_: *mut leanh::LeanObject,
    mut v_post_7015_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7016_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7017_: *mut leanh::LeanObject,
    mut v_skipInstances_7018_: *mut leanh::LeanObject,
    mut v___x_7019_: *mut leanh::LeanObject,
    mut v___y_7020_: *mut leanh::LeanObject,
    mut v_b_7021_: *mut leanh::LeanObject,
    mut v_a_7022_: *mut leanh::LeanObject,
    mut v___y_7023_: *mut leanh::LeanObject,
    mut v___y_7024_: *mut leanh::LeanObject,
    mut v___y_7025_: *mut leanh::LeanObject,
    mut v___y_7026_: *mut leanh::LeanObject,
    mut v___y_7027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7028_: u8 = 0;
    let mut v_skipConstInApp_boxed_7029_: u8 = 0;
    let mut v_skipInstances_boxed_7030_: u8 = 0;
    let mut v_res_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7028_ = (leanh::lean_unbox(v_usedLetOnly_7016_) as u8);
    v_skipConstInApp_boxed_7029_ = (leanh::lean_unbox(v_skipConstInApp_7017_) as u8);
    v_skipInstances_boxed_7030_ = (leanh::lean_unbox(v_skipInstances_7018_) as u8);
    v_res_7031_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__0(v_pre_7014_, v_post_7015_, v_usedLetOnly_boxed_7028_, v_skipConstInApp_boxed_7029_, v_skipInstances_boxed_7030_, v___x_7019_, v___y_7020_, v_b_7021_, v_a_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_);
    leanh::lean_dec(v___y_7026_);
    leanh::lean_dec_ref(v___y_7025_);
    leanh::lean_dec(v___y_7024_);
    leanh::lean_dec_ref(v___y_7023_);
    leanh::lean_dec(v_a_7022_);
    leanh::lean_dec(v___y_7020_);
    return v_res_7031_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg(
    mut v_upperBound_7032_: *mut leanh::LeanObject,
    mut v___x_7033_: *mut leanh::LeanObject,
    mut v_pre_7034_: *mut leanh::LeanObject,
    mut v_post_7035_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7036_: u8,
    mut v_skipConstInApp_7037_: u8,
    mut v_skipInstances_7038_: u8,
    mut v_a_7039_: *mut leanh::LeanObject,
    mut v_b_7040_: *mut leanh::LeanObject,
    mut v___y_7041_: *mut leanh::LeanObject,
    mut v___y_7042_: *mut leanh::LeanObject,
    mut v___y_7043_: *mut leanh::LeanObject,
    mut v___y_7044_: *mut leanh::LeanObject,
    mut v___y_7045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7053_: u8 = 0;
    let mut v_a_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v_a_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7066_: u8 = 0;
    let mut v___x_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7070_: u8 = 0;
    let mut v___x_7071_: u8 = 0;
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: u8 = 0;
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_7081_: u8 = 0;
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7071_ = lean_nat_dec_lt(v_a_7039_, v_upperBound_7032_);
                if v___x_7071_ == 0 {
                    leanh::lean_dec(v_a_7039_);
                    leanh::lean_dec_ref(v_post_7035_);
                    leanh::lean_dec_ref(v_pre_7034_);
                    v___x_7072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7072_, 0, v_b_7040_);
                    return v___x_7072_;
                } else {
                    v___x_7073_ = lean_array_fget_borrowed(v_b_7040_, v_a_7039_);
                    v___x_7074_ = lean_array_get_size(v___x_7033_);
                    v___x_7075_ = lean_nat_dec_lt(v_a_7039_, v___x_7074_);
                    if v___x_7075_ == 0 {
                        leanh::lean_inc(v___x_7073_);
                        v___x_7076_ = leanh::lean_box((v_usedLetOnly_7036_) as usize);
                        v___x_7077_ = leanh::lean_box((v_skipConstInApp_7037_) as usize);
                        v___x_7078_ = leanh::lean_box((v_skipInstances_7038_) as usize);
                        leanh::lean_inc(v_a_7039_);
                        leanh::lean_inc(v___y_7041_);
                        leanh::lean_inc_ref(v_post_7035_);
                        leanh::lean_inc_ref(v_pre_7034_);
                        v___f_7079_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        leanh::lean_closure_set(v___f_7079_, 0, v_pre_7034_);
                        leanh::lean_closure_set(v___f_7079_, 1, v_post_7035_);
                        leanh::lean_closure_set(v___f_7079_, 2, v___x_7076_);
                        leanh::lean_closure_set(v___f_7079_, 3, v___x_7077_);
                        leanh::lean_closure_set(v___f_7079_, 4, v___x_7078_);
                        leanh::lean_closure_set(v___f_7079_, 5, v___x_7073_);
                        leanh::lean_closure_set(v___f_7079_, 6, v___y_7041_);
                        leanh::lean_closure_set(v___f_7079_, 7, v_b_7040_);
                        leanh::lean_closure_set(v___f_7079_, 8, v_a_7039_);
                        v___y_7048_ = v___f_7079_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7080_ = lean_array_fget_borrowed(v___x_7033_, v_a_7039_);
                        v_isInstance_7081_ = leanh::lean_ctor_get_uint8(
                            v___x_7080_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_7081_ == 0 {
                            leanh::lean_inc(v___x_7073_);
                            v___x_7082_ = leanh::lean_box((v_usedLetOnly_7036_) as usize);
                            v___x_7083_ = leanh::lean_box((v_skipConstInApp_7037_) as usize);
                            v___x_7084_ = leanh::lean_box((v_skipInstances_7038_) as usize);
                            leanh::lean_inc(v_a_7039_);
                            leanh::lean_inc(v___y_7041_);
                            leanh::lean_inc_ref(v_post_7035_);
                            leanh::lean_inc_ref(v_pre_7034_);
                            v___f_7085_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                            leanh::lean_closure_set(v___f_7085_, 0, v_pre_7034_);
                            leanh::lean_closure_set(v___f_7085_, 1, v_post_7035_);
                            leanh::lean_closure_set(v___f_7085_, 2, v___x_7082_);
                            leanh::lean_closure_set(v___f_7085_, 3, v___x_7083_);
                            leanh::lean_closure_set(v___f_7085_, 4, v___x_7084_);
                            leanh::lean_closure_set(v___f_7085_, 5, v___x_7073_);
                            leanh::lean_closure_set(v___f_7085_, 6, v___y_7041_);
                            leanh::lean_closure_set(v___f_7085_, 7, v_b_7040_);
                            leanh::lean_closure_set(v___f_7085_, 8, v_a_7039_);
                            v___y_7048_ = v___f_7085_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_7086_, 0, v_b_7040_);
                            v___f_7087_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 1);
                            leanh::lean_closure_set(v___f_7087_, 0, v___x_7086_);
                            v___y_7048_ = v___f_7087_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_7045_);
                leanh::lean_inc_ref(v___y_7044_);
                leanh::lean_inc(v___y_7043_);
                leanh::lean_inc_ref(v___y_7042_);
                v___x_7049_ = leanh::lean_apply_5(
                    v___y_7048_,
                    v___y_7042_,
                    v___y_7043_,
                    v___y_7044_,
                    v___y_7045_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_7049_) == 0 {
                    v_a_7050_ = leanh::lean_ctor_get(v___x_7049_, 0);
                    v_isSharedCheck_7062_ = (!leanh::lean_is_exclusive(v___x_7049_)) as u8;
                    if v_isSharedCheck_7062_ == 0 {
                        v___x_7052_ = v___x_7049_;
                        v_isShared_7053_ = v_isSharedCheck_7062_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7050_);
                        leanh::lean_dec(v___x_7049_);
                        v___x_7052_ = leanh::lean_box(0);
                        v_isShared_7053_ = v_isSharedCheck_7062_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7039_);
                    leanh::lean_dec_ref(v_post_7035_);
                    leanh::lean_dec_ref(v_pre_7034_);
                    v_a_7063_ = leanh::lean_ctor_get(v___x_7049_, 0);
                    v_isSharedCheck_7070_ = (!leanh::lean_is_exclusive(v___x_7049_)) as u8;
                    if v_isSharedCheck_7070_ == 0 {
                        v___x_7065_ = v___x_7049_;
                        v_isShared_7066_ = v_isSharedCheck_7070_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7063_);
                        leanh::lean_dec(v___x_7049_);
                        v___x_7065_ = leanh::lean_box(0);
                        v_isShared_7066_ = v_isSharedCheck_7070_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_7050_) == 0 {
                    leanh::lean_dec(v_a_7039_);
                    leanh::lean_dec_ref(v_post_7035_);
                    leanh::lean_dec_ref(v_pre_7034_);
                    v_a_7054_ = leanh::lean_ctor_get(v_a_7050_, 0);
                    leanh::lean_inc(v_a_7054_);
                    leanh::lean_dec_ref_known(v_a_7050_, 1);
                    if v_isShared_7053_ == 0 {
                        leanh::lean_ctor_set(v___x_7052_, 0, v_a_7054_);
                        v___x_7056_ = v___x_7052_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 0, v_a_7054_);
                        v___x_7056_ = v_reuseFailAlloc_7057_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7052_);
                    v_a_7058_ = leanh::lean_ctor_get(v_a_7050_, 0);
                    leanh::lean_inc(v_a_7058_);
                    leanh::lean_dec_ref_known(v_a_7050_, 1);
                    v___x_7059_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7060_ = lean_nat_add(v_a_7039_, v___x_7059_);
                    leanh::lean_dec(v_a_7039_);
                    v_a_7039_ = v___x_7060_;
                    v_b_7040_ = v_a_7058_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_7056_;
            }
            4 => {
                if v_isShared_7066_ == 0 {
                    v___x_7068_ = v___x_7065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 0, v_a_7063_);
                    v___x_7068_ = v_reuseFailAlloc_7069_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__9(
    mut v_skipInstances_7088_: u8,
    mut v_pre_7089_: *mut leanh::LeanObject,
    mut v_post_7090_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7091_: u8,
    mut v_skipConstInApp_7092_: u8,
    mut v_x_7093_: *mut leanh::LeanObject,
    mut v_x_7094_: *mut leanh::LeanObject,
    mut v_x_7095_: *mut leanh::LeanObject,
    mut v___y_7096_: *mut leanh::LeanObject,
    mut v___y_7097_: *mut leanh::LeanObject,
    mut v___y_7098_: *mut leanh::LeanObject,
    mut v___y_7099_: *mut leanh::LeanObject,
    mut v___y_7100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7109_: usize = 0;
    let mut v___x_7110_: usize = 0;
    let mut v___x_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7118_: u8 = 0;
    let mut v___x_7120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7122_: u8 = 0;
    let mut v___x_7123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7135_: u8 = 0;
    let mut v___x_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7139_: u8 = 0;
    let mut v_a_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7143_: u8 = 0;
    let mut v___x_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7147_: u8 = 0;
    let mut v___x_7149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7093_) == 5 {
                    v_fn_7151_ = leanh::lean_ctor_get(v_x_7093_, 0);
                    leanh::lean_inc_ref(v_fn_7151_);
                    v_arg_7152_ = leanh::lean_ctor_get(v_x_7093_, 1);
                    leanh::lean_inc_ref(v_arg_7152_);
                    leanh::lean_dec_ref_known(v_x_7093_, 2);
                    v___x_7153_ = lean_array_set(v_x_7094_, v_x_7095_, v_arg_7152_);
                    v___x_7154_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7155_ = lean_nat_sub(v_x_7095_, v___x_7154_);
                    leanh::lean_dec(v_x_7095_);
                    v_x_7093_ = v_fn_7151_;
                    v_x_7094_ = v___x_7153_;
                    v_x_7095_ = v___x_7155_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_7095_);
                    if v_skipConstInApp_7092_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_7157_ = l_Lean_Expr_isConst(v_x_7093_);
                        if v___x_7157_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_7103_ = v_x_7093_;
                            v___y_7104_ = v___y_7096_;
                            v___y_7105_ = v___y_7097_;
                            v___y_7106_ = v___y_7098_;
                            v___y_7107_ = v___y_7099_;
                            v___y_7108_ = v___y_7100_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_7088_ == 0 {
                    v_sz_7109_ = lean_array_size(v_x_7094_);
                    v___x_7110_ = 0usize;
                    leanh::lean_inc_ref(v_post_7090_);
                    leanh::lean_inc_ref(v_pre_7089_);
                    v___x_7111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__3(v_pre_7089_, v_post_7090_, v_usedLetOnly_7091_, v_skipConstInApp_7092_, v_skipInstances_7088_, v_sz_7109_, v___x_7110_, v_x_7094_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_);
                    if leanh::lean_obj_tag(v___x_7111_) == 0 {
                        v_a_7112_ = leanh::lean_ctor_get(v___x_7111_, 0);
                        leanh::lean_inc(v_a_7112_);
                        leanh::lean_dec_ref_known(v___x_7111_, 1);
                        v___x_7113_ = l_Lean_mkAppN(v_f_7103_, v_a_7112_);
                        leanh::lean_dec(v_a_7112_);
                        v___x_7114_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7089_, v_post_7090_, v_usedLetOnly_7091_, v_skipConstInApp_7092_, v_skipInstances_7088_, v___x_7113_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_);
                        return v___x_7114_;
                    } else {
                        leanh::lean_dec_ref(v_f_7103_);
                        leanh::lean_dec_ref(v_post_7090_);
                        leanh::lean_dec_ref(v_pre_7089_);
                        v_a_7115_ = leanh::lean_ctor_get(v___x_7111_, 0);
                        v_isSharedCheck_7122_ =
                            (!leanh::lean_is_exclusive(v___x_7111_)) as u8;
                        if v_isSharedCheck_7122_ == 0 {
                            v___x_7117_ = v___x_7111_;
                            v_isShared_7118_ = v_isSharedCheck_7122_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7115_);
                            leanh::lean_dec(v___x_7111_);
                            v___x_7117_ = leanh::lean_box(0);
                            v_isShared_7118_ = v_isSharedCheck_7122_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_7123_ = lean_array_get_size(v_x_7094_);
                    leanh::lean_inc_ref(v_f_7103_);
                    v___x_7124_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_7103_,
                        v___x_7123_,
                        v___y_7105_,
                        v___y_7106_,
                        v___y_7107_,
                        v___y_7108_,
                    );
                    if leanh::lean_obj_tag(v___x_7124_) == 0 {
                        v_a_7125_ = leanh::lean_ctor_get(v___x_7124_, 0);
                        leanh::lean_inc(v_a_7125_);
                        leanh::lean_dec_ref_known(v___x_7124_, 1);
                        v_paramInfo_7126_ = leanh::lean_ctor_get(v_a_7125_, 0);
                        leanh::lean_inc_ref(v_paramInfo_7126_);
                        leanh::lean_dec(v_a_7125_);
                        v___x_7127_ = leanh::lean_unsigned_to_nat(0);
                        leanh::lean_inc_ref(v_post_7090_);
                        leanh::lean_inc_ref(v_pre_7089_);
                        v___x_7128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg(v___x_7123_, v_paramInfo_7126_, v_pre_7089_, v_post_7090_, v_usedLetOnly_7091_, v_skipConstInApp_7092_, v_skipInstances_7088_, v___x_7127_, v_x_7094_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_);
                        leanh::lean_dec_ref(v_paramInfo_7126_);
                        if leanh::lean_obj_tag(v___x_7128_) == 0 {
                            v_a_7129_ = leanh::lean_ctor_get(v___x_7128_, 0);
                            leanh::lean_inc(v_a_7129_);
                            leanh::lean_dec_ref_known(v___x_7128_, 1);
                            v___x_7130_ = l_Lean_mkAppN(v_f_7103_, v_a_7129_);
                            leanh::lean_dec(v_a_7129_);
                            v___x_7131_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7089_, v_post_7090_, v_usedLetOnly_7091_, v_skipConstInApp_7092_, v_skipInstances_7088_, v___x_7130_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_);
                            return v___x_7131_;
                        } else {
                            leanh::lean_dec_ref(v_f_7103_);
                            leanh::lean_dec_ref(v_post_7090_);
                            leanh::lean_dec_ref(v_pre_7089_);
                            v_a_7132_ = leanh::lean_ctor_get(v___x_7128_, 0);
                            v_isSharedCheck_7139_ =
                                (!leanh::lean_is_exclusive(v___x_7128_)) as u8;
                            if v_isSharedCheck_7139_ == 0 {
                                v___x_7134_ = v___x_7128_;
                                v_isShared_7135_ = v_isSharedCheck_7139_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7132_);
                                leanh::lean_dec(v___x_7128_);
                                v___x_7134_ = leanh::lean_box(0);
                                v_isShared_7135_ = v_isSharedCheck_7139_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_f_7103_);
                        leanh::lean_dec_ref(v_x_7094_);
                        leanh::lean_dec_ref(v_post_7090_);
                        leanh::lean_dec_ref(v_pre_7089_);
                        v_a_7140_ = leanh::lean_ctor_get(v___x_7124_, 0);
                        v_isSharedCheck_7147_ =
                            (!leanh::lean_is_exclusive(v___x_7124_)) as u8;
                        if v_isSharedCheck_7147_ == 0 {
                            v___x_7142_ = v___x_7124_;
                            v_isShared_7143_ = v_isSharedCheck_7147_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7140_);
                            leanh::lean_dec(v___x_7124_);
                            v___x_7142_ = leanh::lean_box(0);
                            v_isShared_7143_ = v_isSharedCheck_7147_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_7118_ == 0 {
                    v___x_7120_ = v___x_7117_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7121_, 0, v_a_7115_);
                    v___x_7120_ = v_reuseFailAlloc_7121_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7120_;
            }
            4 => {
                if v_isShared_7135_ == 0 {
                    v___x_7137_ = v___x_7134_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7138_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7138_, 0, v_a_7132_);
                    v___x_7137_ = v_reuseFailAlloc_7138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7137_;
            }
            6 => {
                if v_isShared_7143_ == 0 {
                    v___x_7145_ = v___x_7142_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7146_, 0, v_a_7140_);
                    v___x_7145_ = v_reuseFailAlloc_7146_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7145_;
            }
            8 => {
                leanh::lean_inc_ref(v_post_7090_);
                leanh::lean_inc_ref(v_pre_7089_);
                v___x_7149_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7089_, v_post_7090_, v_usedLetOnly_7091_, v_skipConstInApp_7092_, v_skipInstances_7088_, v_x_7093_, v___y_7096_, v___y_7097_, v___y_7098_, v___y_7099_, v___y_7100_);
                if leanh::lean_obj_tag(v___x_7149_) == 0 {
                    v_a_7150_ = leanh::lean_ctor_get(v___x_7149_, 0);
                    leanh::lean_inc(v_a_7150_);
                    leanh::lean_dec_ref_known(v___x_7149_, 1);
                    v_f_7103_ = v_a_7150_;
                    v___y_7104_ = v___y_7096_;
                    v___y_7105_ = v___y_7097_;
                    v___y_7106_ = v___y_7098_;
                    v___y_7107_ = v___y_7099_;
                    v___y_7108_ = v___y_7100_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_x_7094_);
                    leanh::lean_dec_ref(v_post_7090_);
                    leanh::lean_dec_ref(v_pre_7089_);
                    return v___x_7149_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__1(
    mut v___x_7158_: *mut leanh::LeanObject,
    mut v_pre_7159_: *mut leanh::LeanObject,
    mut v_e_7160_: *mut leanh::LeanObject,
    mut v_post_7161_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7162_: u8,
    mut v_skipConstInApp_7163_: u8,
    mut v_skipInstances_7164_: u8,
    mut v___y_7165_: *mut leanh::LeanObject,
    mut v___y_7166_: *mut leanh::LeanObject,
    mut v___y_7167_: *mut leanh::LeanObject,
    mut v___y_7168_: *mut leanh::LeanObject,
    mut v___y_7169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7176_: u8 = 0;
    let mut v___y_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: usize = 0;
    let mut v___x_7196_: usize = 0;
    let mut v___x_7197_: u8 = 0;
    let mut v___x_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: usize = 0;
    let mut v___x_7207_: usize = 0;
    let mut v___x_7208_: u8 = 0;
    let mut v___x_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7221_: u8 = 0;
    let mut v_a_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7225_: u8 = 0;
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7229_: u8 = 0;
    let mut v_a_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7233_: u8 = 0;
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7171_ = l_Lean_Core_checkSystem(v___x_7158_, v___y_7168_, v___y_7169_);
                if leanh::lean_obj_tag(v___x_7171_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7171_, 1);
                    leanh::lean_inc_ref(v_pre_7159_);
                    leanh::lean_inc(v___y_7169_);
                    leanh::lean_inc_ref(v___y_7168_);
                    leanh::lean_inc(v___y_7167_);
                    leanh::lean_inc_ref(v___y_7166_);
                    leanh::lean_inc_ref(v_e_7160_);
                    v___x_7172_ = leanh::lean_apply_6(
                        v_pre_7159_,
                        v_e_7160_,
                        v___y_7166_,
                        v___y_7167_,
                        v___y_7168_,
                        v___y_7169_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_7172_) == 0 {
                        v_a_7173_ = leanh::lean_ctor_get(v___x_7172_, 0);
                        v_isSharedCheck_7221_ =
                            (!leanh::lean_is_exclusive(v___x_7172_)) as u8;
                        if v_isSharedCheck_7221_ == 0 {
                            v___x_7175_ = v___x_7172_;
                            v_isShared_7176_ = v_isSharedCheck_7221_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7173_);
                            leanh::lean_dec(v___x_7172_);
                            v___x_7175_ = leanh::lean_box(0);
                            v_isShared_7176_ = v_isSharedCheck_7221_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_7161_);
                        leanh::lean_dec_ref(v_e_7160_);
                        leanh::lean_dec_ref(v_pre_7159_);
                        v_a_7222_ = leanh::lean_ctor_get(v___x_7172_, 0);
                        v_isSharedCheck_7229_ =
                            (!leanh::lean_is_exclusive(v___x_7172_)) as u8;
                        if v_isSharedCheck_7229_ == 0 {
                            v___x_7224_ = v___x_7172_;
                            v_isShared_7225_ = v_isSharedCheck_7229_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7222_);
                            leanh::lean_dec(v___x_7172_);
                            v___x_7224_ = leanh::lean_box(0);
                            v_isShared_7225_ = v_isSharedCheck_7229_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_7161_);
                    leanh::lean_dec_ref(v_e_7160_);
                    leanh::lean_dec_ref(v_pre_7159_);
                    v_a_7230_ = leanh::lean_ctor_get(v___x_7171_, 0);
                    v_isSharedCheck_7237_ = (!leanh::lean_is_exclusive(v___x_7171_)) as u8;
                    if v_isSharedCheck_7237_ == 0 {
                        v___x_7232_ = v___x_7171_;
                        v_isShared_7233_ = v_isSharedCheck_7237_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7230_);
                        leanh::lean_dec(v___x_7171_);
                        v___x_7232_ = leanh::lean_box(0);
                        v_isShared_7233_ = v_isSharedCheck_7237_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_7173_) {
                0 => {
                    leanh::lean_dec_ref(v_post_7161_);
                    leanh::lean_dec_ref(v_e_7160_);
                    leanh::lean_dec_ref(v_pre_7159_);
                    v_e_7213_ = leanh::lean_ctor_get(v_a_7173_, 0);
                    leanh::lean_inc_ref(v_e_7213_);
                    leanh::lean_dec_ref_known(v_a_7173_, 1);
                    if v_isShared_7176_ == 0 {
                        leanh::lean_ctor_set(v___x_7175_, 0, v_e_7213_);
                        v___x_7215_ = v___x_7175_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7216_, 0, v_e_7213_);
                        v___x_7215_ = v_reuseFailAlloc_7216_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_7175_);
                    leanh::lean_dec_ref(v_e_7160_);
                    v_e_7217_ = leanh::lean_ctor_get(v_a_7173_, 0);
                    leanh::lean_inc_ref(v_e_7217_);
                    leanh::lean_dec_ref_known(v_a_7173_, 1);
                    v___x_7218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v_e_7217_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    return v___x_7218_;
                }
                _ => {
                    leanh::lean_del_object(v___x_7175_);
                    v_e_x3f_7219_ = leanh::lean_ctor_get(v_a_7173_, 0);
                    leanh::lean_inc(v_e_x3f_7219_);
                    leanh::lean_dec_ref_known(v_a_7173_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_7219_) == 0 {
                        v___y_7178_ = v_e_7160_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_7160_);
                        v_val_7220_ = leanh::lean_ctor_get(v_e_x3f_7219_, 0);
                        leanh::lean_inc(v_val_7220_);
                        leanh::lean_dec_ref_known(v_e_x3f_7219_, 1);
                        v___y_7178_ = v_val_7220_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match leanh::lean_obj_tag(v___y_7178_) {
                7 => {
                    v___x_7179_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
                    v___x_7180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___x_7179_, v___y_7178_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    return v___x_7180_;
                }
                6 => {
                    v___x_7181_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
                    v___x_7182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___x_7181_, v___y_7178_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    return v___x_7182_;
                }
                8 => {
                    v___x_7183_ = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
                    v___x_7184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___x_7183_, v___y_7178_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    return v___x_7184_;
                }
                5 => {
                    v_dummy_7185_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1,
                    );
                    v_nargs_7186_ = l_Lean_Expr_getAppNumArgs(v___y_7178_);
                    leanh::lean_inc(v_nargs_7186_);
                    v___x_7187_ = lean_mk_array(v_nargs_7186_, v_dummy_7185_);
                    v___x_7188_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7189_ = lean_nat_sub(v_nargs_7186_, v___x_7188_);
                    leanh::lean_dec(v_nargs_7186_);
                    v___x_7190_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__9(v_skipInstances_7164_, v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v___y_7178_, v___x_7187_, v___x_7189_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    return v___x_7190_;
                }
                10 => {
                    v_data_7191_ = leanh::lean_ctor_get(v___y_7178_, 0);
                    v_expr_7192_ = leanh::lean_ctor_get(v___y_7178_, 1);
                    leanh::lean_inc_ref(v_expr_7192_);
                    leanh::lean_inc_ref(v_post_7161_);
                    leanh::lean_inc_ref(v_pre_7159_);
                    v___x_7193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v_expr_7192_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    if leanh::lean_obj_tag(v___x_7193_) == 0 {
                        v_a_7194_ = leanh::lean_ctor_get(v___x_7193_, 0);
                        leanh::lean_inc(v_a_7194_);
                        leanh::lean_dec_ref_known(v___x_7193_, 1);
                        v___x_7195_ = lean_ptr_addr(v_expr_7192_);
                        v___x_7196_ = lean_ptr_addr(v_a_7194_);
                        v___x_7197_ = lean_usize_dec_eq(v___x_7195_, v___x_7196_);
                        if v___x_7197_ == 0 {
                            leanh::lean_inc(v_data_7191_);
                            leanh::lean_dec_ref_known(v___y_7178_, 2);
                            v___x_7198_ = l_Lean_Expr_mdata___override(v_data_7191_, v_a_7194_);
                            v___x_7199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___x_7198_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                            return v___x_7199_;
                        } else {
                            leanh::lean_dec(v_a_7194_);
                            v___x_7200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___y_7178_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                            return v___x_7200_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_7178_, 2);
                        leanh::lean_dec_ref(v_post_7161_);
                        leanh::lean_dec_ref(v_pre_7159_);
                        return v___x_7193_;
                    }
                }
                11 => {
                    v_typeName_7201_ = leanh::lean_ctor_get(v___y_7178_, 0);
                    v_idx_7202_ = leanh::lean_ctor_get(v___y_7178_, 1);
                    v_struct_7203_ = leanh::lean_ctor_get(v___y_7178_, 2);
                    leanh::lean_inc_ref(v_struct_7203_);
                    leanh::lean_inc_ref(v_post_7161_);
                    leanh::lean_inc_ref(v_pre_7159_);
                    v___x_7204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v_struct_7203_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    if leanh::lean_obj_tag(v___x_7204_) == 0 {
                        v_a_7205_ = leanh::lean_ctor_get(v___x_7204_, 0);
                        leanh::lean_inc(v_a_7205_);
                        leanh::lean_dec_ref_known(v___x_7204_, 1);
                        v___x_7206_ = lean_ptr_addr(v_struct_7203_);
                        v___x_7207_ = lean_ptr_addr(v_a_7205_);
                        v___x_7208_ = lean_usize_dec_eq(v___x_7206_, v___x_7207_);
                        if v___x_7208_ == 0 {
                            leanh::lean_inc(v_idx_7202_);
                            leanh::lean_inc(v_typeName_7201_);
                            leanh::lean_dec_ref_known(v___y_7178_, 3);
                            v___x_7209_ = l_Lean_Expr_proj___override(
                                v_typeName_7201_,
                                v_idx_7202_,
                                v_a_7205_,
                            );
                            v___x_7210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___x_7209_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                            return v___x_7210_;
                        } else {
                            leanh::lean_dec(v_a_7205_);
                            v___x_7211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___y_7178_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                            return v___x_7211_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_7178_, 3);
                        leanh::lean_dec_ref(v_post_7161_);
                        leanh::lean_dec_ref(v_pre_7159_);
                        return v___x_7204_;
                    }
                }
                _ => {
                    v___x_7212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7159_, v_post_7161_, v_usedLetOnly_7162_, v_skipConstInApp_7163_, v_skipInstances_7164_, v___y_7178_, v___y_7165_, v___y_7166_, v___y_7167_, v___y_7168_, v___y_7169_);
                    return v___x_7212_;
                }
            },
            3 => {
                return v___x_7215_;
            }
            4 => {
                if v_isShared_7225_ == 0 {
                    v___x_7227_ = v___x_7224_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 0, v_a_7222_);
                    v___x_7227_ = v_reuseFailAlloc_7228_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7227_;
            }
            6 => {
                if v_isShared_7233_ == 0 {
                    v___x_7235_ = v___x_7232_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7236_, 0, v_a_7230_);
                    v___x_7235_ = v_reuseFailAlloc_7236_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__1___boxed(
    mut v___x_7238_: *mut leanh::LeanObject,
    mut v_pre_7239_: *mut leanh::LeanObject,
    mut v_e_7240_: *mut leanh::LeanObject,
    mut v_post_7241_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7242_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7243_: *mut leanh::LeanObject,
    mut v_skipInstances_7244_: *mut leanh::LeanObject,
    mut v___y_7245_: *mut leanh::LeanObject,
    mut v___y_7246_: *mut leanh::LeanObject,
    mut v___y_7247_: *mut leanh::LeanObject,
    mut v___y_7248_: *mut leanh::LeanObject,
    mut v___y_7249_: *mut leanh::LeanObject,
    mut v___y_7250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7251_: u8 = 0;
    let mut v_skipConstInApp_boxed_7252_: u8 = 0;
    let mut v_skipInstances_boxed_7253_: u8 = 0;
    let mut v_res_7254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7251_ = (leanh::lean_unbox(v_usedLetOnly_7242_) as u8);
    v_skipConstInApp_boxed_7252_ = (leanh::lean_unbox(v_skipConstInApp_7243_) as u8);
    v_skipInstances_boxed_7253_ = (leanh::lean_unbox(v_skipInstances_7244_) as u8);
    v_res_7254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__1(v___x_7238_, v_pre_7239_, v_e_7240_, v_post_7241_, v_usedLetOnly_boxed_7251_, v_skipConstInApp_boxed_7252_, v_skipInstances_boxed_7253_, v___y_7245_, v___y_7246_, v___y_7247_, v___y_7248_, v___y_7249_);
    leanh::lean_dec(v___y_7249_);
    leanh::lean_dec_ref(v___y_7248_);
    leanh::lean_dec(v___y_7247_);
    leanh::lean_dec_ref(v___y_7246_);
    leanh::lean_dec(v___y_7245_);
    return v_res_7254_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(
    mut v_pre_7255_: *mut leanh::LeanObject,
    mut v_post_7256_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7257_: u8,
    mut v_skipConstInApp_7258_: u8,
    mut v_skipInstances_7259_: u8,
    mut v_e_7260_: *mut leanh::LeanObject,
    mut v_a_7261_: *mut leanh::LeanObject,
    mut v___y_7262_: *mut leanh::LeanObject,
    mut v___y_7263_: *mut leanh::LeanObject,
    mut v___y_7264_: *mut leanh::LeanObject,
    mut v___y_7265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7272_: u8 = 0;
    let mut v___x_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7285_: u8 = 0;
    let mut v___x_7287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7289_: u8 = 0;
    let mut v_unused_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7294_: u8 = 0;
    let mut v___x_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7298_: u8 = 0;
    let mut v_val_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7303_: u8 = 0;
    let mut v_a_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7307_: u8 = 0;
    let mut v___x_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_7261_);
                v___x_7267_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_7267_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7267_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7267_, 2, v_a_7261_);
                v___x_7268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__0(leanh::lean_box(0), v___x_7267_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
                if leanh::lean_obj_tag(v___x_7268_) == 0 {
                    v_a_7269_ = leanh::lean_ctor_get(v___x_7268_, 0);
                    v_isSharedCheck_7303_ = (!leanh::lean_is_exclusive(v___x_7268_)) as u8;
                    if v_isSharedCheck_7303_ == 0 {
                        v___x_7271_ = v___x_7268_;
                        v_isShared_7272_ = v_isSharedCheck_7303_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7269_);
                        leanh::lean_dec(v___x_7268_);
                        v___x_7271_ = leanh::lean_box(0);
                        v_isShared_7272_ = v_isSharedCheck_7303_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7260_);
                    leanh::lean_dec_ref(v_post_7256_);
                    leanh::lean_dec_ref(v_pre_7255_);
                    v_a_7304_ = leanh::lean_ctor_get(v___x_7268_, 0);
                    v_isSharedCheck_7311_ = (!leanh::lean_is_exclusive(v___x_7268_)) as u8;
                    if v_isSharedCheck_7311_ == 0 {
                        v___x_7306_ = v___x_7268_;
                        v_isShared_7307_ = v_isSharedCheck_7311_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7304_);
                        leanh::lean_dec(v___x_7268_);
                        v___x_7306_ = leanh::lean_box(0);
                        v_isShared_7307_ = v_isSharedCheck_7311_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2_spec__6___redArg(v_a_7269_, v_e_7260_);
                leanh::lean_dec(v_a_7269_);
                if leanh::lean_obj_tag(v___x_7273_) == 0 {
                    leanh::lean_del_object(v___x_7271_);
                    v___x_7274_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___closed__0;
                    v___x_7275_ = leanh::lean_box((v_usedLetOnly_7257_) as usize);
                    v___x_7276_ = leanh::lean_box((v_skipConstInApp_7258_) as usize);
                    v___x_7277_ = leanh::lean_box((v_skipInstances_7259_) as usize);
                    leanh::lean_inc_ref(v_e_7260_);
                    v___f_7278_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__1___boxed as *mut core::ffi::c_void, 13, 7);
                    leanh::lean_closure_set(v___f_7278_, 0, v___x_7274_);
                    leanh::lean_closure_set(v___f_7278_, 1, v_pre_7255_);
                    leanh::lean_closure_set(v___f_7278_, 2, v_e_7260_);
                    leanh::lean_closure_set(v___f_7278_, 3, v_post_7256_);
                    leanh::lean_closure_set(v___f_7278_, 4, v___x_7275_);
                    leanh::lean_closure_set(v___f_7278_, 5, v___x_7276_);
                    leanh::lean_closure_set(v___f_7278_, 6, v___x_7277_);
                    v___x_7279_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10___redArg(v___f_7278_, v_a_7261_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
                    if leanh::lean_obj_tag(v___x_7279_) == 0 {
                        v_a_7280_ = leanh::lean_ctor_get(v___x_7279_, 0);
                        leanh::lean_inc_n(v_a_7280_, 2);
                        leanh::lean_dec_ref_known(v___x_7279_, 1);
                        leanh::lean_inc(v_a_7261_);
                        v___f_7281_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1_spec__2___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_7281_, 0, v_a_7261_);
                        leanh::lean_closure_set(v___f_7281_, 1, v_e_7260_);
                        leanh::lean_closure_set(v___f_7281_, 2, v_a_7280_);
                        v___x_7282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___lam__0(leanh::lean_box(0), v___f_7281_, v___y_7262_, v___y_7263_, v___y_7264_, v___y_7265_);
                        if leanh::lean_obj_tag(v___x_7282_) == 0 {
                            v_isSharedCheck_7289_ =
                                (!leanh::lean_is_exclusive(v___x_7282_)) as u8;
                            if v_isSharedCheck_7289_ == 0 {
                                v_unused_7290_ = leanh::lean_ctor_get(v___x_7282_, 0);
                                leanh::lean_dec(v_unused_7290_);
                                v___x_7284_ = v___x_7282_;
                                v_isShared_7285_ = v_isSharedCheck_7289_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7282_);
                                v___x_7284_ = leanh::lean_box(0);
                                v_isShared_7285_ = v_isSharedCheck_7289_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7280_);
                            v_a_7291_ = leanh::lean_ctor_get(v___x_7282_, 0);
                            v_isSharedCheck_7298_ =
                                (!leanh::lean_is_exclusive(v___x_7282_)) as u8;
                            if v_isSharedCheck_7298_ == 0 {
                                v___x_7293_ = v___x_7282_;
                                v_isShared_7294_ = v_isSharedCheck_7298_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7291_);
                                leanh::lean_dec(v___x_7282_);
                                v___x_7293_ = leanh::lean_box(0);
                                v_isShared_7294_ = v_isSharedCheck_7298_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7260_);
                        return v___x_7279_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7260_);
                    leanh::lean_dec_ref(v_post_7256_);
                    leanh::lean_dec_ref(v_pre_7255_);
                    v_val_7299_ = leanh::lean_ctor_get(v___x_7273_, 0);
                    leanh::lean_inc(v_val_7299_);
                    leanh::lean_dec_ref_known(v___x_7273_, 1);
                    if v_isShared_7272_ == 0 {
                        leanh::lean_ctor_set(v___x_7271_, 0, v_val_7299_);
                        v___x_7301_ = v___x_7271_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7302_, 0, v_val_7299_);
                        v___x_7301_ = v_reuseFailAlloc_7302_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7285_ == 0 {
                    leanh::lean_ctor_set(v___x_7284_, 0, v_a_7280_);
                    v___x_7287_ = v___x_7284_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7288_, 0, v_a_7280_);
                    v___x_7287_ = v_reuseFailAlloc_7288_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7287_;
            }
            4 => {
                if v_isShared_7294_ == 0 {
                    v___x_7296_ = v___x_7293_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7297_, 0, v_a_7291_);
                    v___x_7296_ = v_reuseFailAlloc_7297_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7296_;
            }
            6 => {
                return v___x_7301_;
            }
            7 => {
                if v_isShared_7307_ == 0 {
                    v___x_7309_ = v___x_7306_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7310_, 0, v_a_7304_);
                    v___x_7309_ = v_reuseFailAlloc_7310_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6___lam__0___boxed(
    mut v_fvars_7312_: *mut leanh::LeanObject,
    mut v_pre_7313_: *mut leanh::LeanObject,
    mut v_post_7314_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7315_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7316_: *mut leanh::LeanObject,
    mut v_skipInstances_7317_: *mut leanh::LeanObject,
    mut v_body_7318_: *mut leanh::LeanObject,
    mut v_x_7319_: *mut leanh::LeanObject,
    mut v___y_7320_: *mut leanh::LeanObject,
    mut v___y_7321_: *mut leanh::LeanObject,
    mut v___y_7322_: *mut leanh::LeanObject,
    mut v___y_7323_: *mut leanh::LeanObject,
    mut v___y_7324_: *mut leanh::LeanObject,
    mut v___y_7325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7326_: u8 = 0;
    let mut v_skipConstInApp_boxed_7327_: u8 = 0;
    let mut v_skipInstances_boxed_7328_: u8 = 0;
    let mut v_res_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7326_ = (leanh::lean_unbox(v_usedLetOnly_7315_) as u8);
    v_skipConstInApp_boxed_7327_ = (leanh::lean_unbox(v_skipConstInApp_7316_) as u8);
    v_skipInstances_boxed_7328_ = (leanh::lean_unbox(v_skipInstances_7317_) as u8);
    v_res_7329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6___lam__0(v_fvars_7312_, v_pre_7313_, v_post_7314_, v_usedLetOnly_boxed_7326_, v_skipConstInApp_boxed_7327_, v_skipInstances_boxed_7328_, v_body_7318_, v_x_7319_, v___y_7320_, v___y_7321_, v___y_7322_, v___y_7323_, v___y_7324_);
    leanh::lean_dec(v___y_7324_);
    leanh::lean_dec_ref(v___y_7323_);
    leanh::lean_dec(v___y_7322_);
    leanh::lean_dec_ref(v___y_7321_);
    leanh::lean_dec(v___y_7320_);
    return v_res_7329_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6(
    mut v_pre_7330_: *mut leanh::LeanObject,
    mut v_post_7331_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7332_: u8,
    mut v_skipConstInApp_7333_: u8,
    mut v_skipInstances_7334_: u8,
    mut v_fvars_7335_: *mut leanh::LeanObject,
    mut v_e_7336_: *mut leanh::LeanObject,
    mut v_a_7337_: *mut leanh::LeanObject,
    mut v___y_7338_: *mut leanh::LeanObject,
    mut v___y_7339_: *mut leanh::LeanObject,
    mut v___y_7340_: *mut leanh::LeanObject,
    mut v___y_7341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_7336_) == 7 {
        let mut v_binderName_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7345_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7346_: u8 = 0;
        let mut v___x_7347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7348_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binderName_7343_ = leanh::lean_ctor_get(v_e_7336_, 0);
        leanh::lean_inc(v_binderName_7343_);
        v_binderType_7344_ = leanh::lean_ctor_get(v_e_7336_, 1);
        leanh::lean_inc_ref(v_binderType_7344_);
        v_body_7345_ = leanh::lean_ctor_get(v_e_7336_, 2);
        leanh::lean_inc_ref(v_body_7345_);
        v_binderInfo_7346_ = leanh::lean_ctor_get_uint8(
            v_e_7336_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        );
        leanh::lean_dec_ref_known(v_e_7336_, 3);
        v___x_7347_ = lean_expr_instantiate_rev(v_binderType_7344_, v_fvars_7335_);
        leanh::lean_dec_ref(v_binderType_7344_);
        leanh::lean_inc_ref(v_post_7331_);
        leanh::lean_inc_ref(v_pre_7330_);
        v___x_7348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7330_, v_post_7331_, v_usedLetOnly_7332_, v_skipConstInApp_7333_, v_skipInstances_7334_, v___x_7347_, v_a_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_);
        if leanh::lean_obj_tag(v___x_7348_) == 0 {
            let mut v_a_7349_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7354_: u8 = 0;
            let mut v___x_7355_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_7349_ = leanh::lean_ctor_get(v___x_7348_, 0);
            leanh::lean_inc(v_a_7349_);
            leanh::lean_dec_ref_known(v___x_7348_, 1);
            v___x_7350_ = leanh::lean_box((v_usedLetOnly_7332_) as usize);
            v___x_7351_ = leanh::lean_box((v_skipConstInApp_7333_) as usize);
            v___x_7352_ = leanh::lean_box((v_skipInstances_7334_) as usize);
            v___f_7353_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            leanh::lean_closure_set(v___f_7353_, 0, v_fvars_7335_);
            leanh::lean_closure_set(v___f_7353_, 1, v_pre_7330_);
            leanh::lean_closure_set(v___f_7353_, 2, v_post_7331_);
            leanh::lean_closure_set(v___f_7353_, 3, v___x_7350_);
            leanh::lean_closure_set(v___f_7353_, 4, v___x_7351_);
            leanh::lean_closure_set(v___f_7353_, 5, v___x_7352_);
            leanh::lean_closure_set(v___f_7353_, 6, v_body_7345_);
            v___x_7354_ = 0;
            v___x_7355_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg(v_binderName_7343_, v_binderInfo_7346_, v_a_7349_, v___f_7353_, v___x_7354_, v_a_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_);
            return v___x_7355_;
        } else {
            leanh::lean_dec_ref(v_body_7345_);
            leanh::lean_dec(v_binderName_7343_);
            leanh::lean_dec_ref(v_fvars_7335_);
            leanh::lean_dec_ref(v_post_7331_);
            leanh::lean_dec_ref(v_pre_7330_);
            return v___x_7348_;
        }
    } else {
        let mut v___x_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7356_ = lean_expr_instantiate_rev(v_e_7336_, v_fvars_7335_);
        leanh::lean_dec_ref(v_e_7336_);
        leanh::lean_inc_ref(v_post_7331_);
        leanh::lean_inc_ref(v_pre_7330_);
        v___x_7357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7330_, v_post_7331_, v_usedLetOnly_7332_, v_skipConstInApp_7333_, v_skipInstances_7334_, v___x_7356_, v_a_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_);
        if leanh::lean_obj_tag(v___x_7357_) == 0 {
            let mut v_a_7358_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7359_: u8 = 0;
            let mut v___x_7360_: u8 = 0;
            let mut v___x_7361_: u8 = 0;
            let mut v___x_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_7358_ = leanh::lean_ctor_get(v___x_7357_, 0);
            leanh::lean_inc(v_a_7358_);
            leanh::lean_dec_ref_known(v___x_7357_, 1);
            v___x_7359_ = 0;
            v___x_7360_ = 1;
            v___x_7361_ = 1;
            v___x_7362_ = l_Lean_Meta_mkForallFVars(
                v_fvars_7335_,
                v_a_7358_,
                v___x_7359_,
                v_usedLetOnly_7332_,
                v___x_7360_,
                v___x_7361_,
                v___y_7338_,
                v___y_7339_,
                v___y_7340_,
                v___y_7341_,
            );
            leanh::lean_dec_ref(v_fvars_7335_);
            if leanh::lean_obj_tag(v___x_7362_) == 0 {
                let mut v_a_7363_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_7363_ = leanh::lean_ctor_get(v___x_7362_, 0);
                leanh::lean_inc(v_a_7363_);
                leanh::lean_dec_ref_known(v___x_7362_, 1);
                v___x_7364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7330_, v_post_7331_, v_usedLetOnly_7332_, v_skipConstInApp_7333_, v_skipInstances_7334_, v_a_7363_, v_a_7337_, v___y_7338_, v___y_7339_, v___y_7340_, v___y_7341_);
                return v___x_7364_;
            } else {
                leanh::lean_dec_ref(v_post_7331_);
                leanh::lean_dec_ref(v_pre_7330_);
                return v___x_7362_;
            }
        } else {
            leanh::lean_dec_ref(v_fvars_7335_);
            leanh::lean_dec_ref(v_post_7331_);
            leanh::lean_dec_ref(v_pre_7330_);
            return v___x_7357_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6___lam__0(
    mut v_fvars_7365_: *mut leanh::LeanObject,
    mut v_pre_7366_: *mut leanh::LeanObject,
    mut v_post_7367_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7368_: u8,
    mut v_skipConstInApp_7369_: u8,
    mut v_skipInstances_7370_: u8,
    mut v_body_7371_: *mut leanh::LeanObject,
    mut v_x_7372_: *mut leanh::LeanObject,
    mut v___y_7373_: *mut leanh::LeanObject,
    mut v___y_7374_: *mut leanh::LeanObject,
    mut v___y_7375_: *mut leanh::LeanObject,
    mut v___y_7376_: *mut leanh::LeanObject,
    mut v___y_7377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7379_ = lean_array_push(v_fvars_7365_, v_x_7372_);
    v___x_7380_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6(v_pre_7366_, v_post_7367_, v_usedLetOnly_7368_, v_skipConstInApp_7369_, v_skipInstances_7370_, v___x_7379_, v_body_7371_, v___y_7373_, v___y_7374_, v___y_7375_, v___y_7376_, v___y_7377_);
    return v___x_7380_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4___boxed(
    mut v_pre_7381_: *mut leanh::LeanObject,
    mut v_post_7382_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7383_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7384_: *mut leanh::LeanObject,
    mut v_skipInstances_7385_: *mut leanh::LeanObject,
    mut v_e_7386_: *mut leanh::LeanObject,
    mut v_a_7387_: *mut leanh::LeanObject,
    mut v___y_7388_: *mut leanh::LeanObject,
    mut v___y_7389_: *mut leanh::LeanObject,
    mut v___y_7390_: *mut leanh::LeanObject,
    mut v___y_7391_: *mut leanh::LeanObject,
    mut v___y_7392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7393_: u8 = 0;
    let mut v_skipConstInApp_boxed_7394_: u8 = 0;
    let mut v_skipInstances_boxed_7395_: u8 = 0;
    let mut v_res_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7393_ = (leanh::lean_unbox(v_usedLetOnly_7383_) as u8);
    v_skipConstInApp_boxed_7394_ = (leanh::lean_unbox(v_skipConstInApp_7384_) as u8);
    v_skipInstances_boxed_7395_ = (leanh::lean_unbox(v_skipInstances_7385_) as u8);
    v_res_7396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__4(v_pre_7381_, v_post_7382_, v_usedLetOnly_boxed_7393_, v_skipConstInApp_boxed_7394_, v_skipInstances_boxed_7395_, v_e_7386_, v_a_7387_, v___y_7388_, v___y_7389_, v___y_7390_, v___y_7391_);
    leanh::lean_dec(v___y_7391_);
    leanh::lean_dec_ref(v___y_7390_);
    leanh::lean_dec(v___y_7389_);
    leanh::lean_dec_ref(v___y_7388_);
    leanh::lean_dec(v_a_7387_);
    return v_res_7396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__3___boxed(
    mut v_pre_7397_: *mut leanh::LeanObject,
    mut v_post_7398_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7399_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7400_: *mut leanh::LeanObject,
    mut v_skipInstances_7401_: *mut leanh::LeanObject,
    mut v_sz_7402_: *mut leanh::LeanObject,
    mut v_i_7403_: *mut leanh::LeanObject,
    mut v_bs_7404_: *mut leanh::LeanObject,
    mut v___y_7405_: *mut leanh::LeanObject,
    mut v___y_7406_: *mut leanh::LeanObject,
    mut v___y_7407_: *mut leanh::LeanObject,
    mut v___y_7408_: *mut leanh::LeanObject,
    mut v___y_7409_: *mut leanh::LeanObject,
    mut v___y_7410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7411_: u8 = 0;
    let mut v_skipConstInApp_boxed_7412_: u8 = 0;
    let mut v_skipInstances_boxed_7413_: u8 = 0;
    let mut v_sz_boxed_7414_: usize = 0;
    let mut v_i_boxed_7415_: usize = 0;
    let mut v_res_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7411_ = (leanh::lean_unbox(v_usedLetOnly_7399_) as u8);
    v_skipConstInApp_boxed_7412_ = (leanh::lean_unbox(v_skipConstInApp_7400_) as u8);
    v_skipInstances_boxed_7413_ = (leanh::lean_unbox(v_skipInstances_7401_) as u8);
    v_sz_boxed_7414_ = leanh::lean_unbox_usize(v_sz_7402_);
    leanh::lean_dec(v_sz_7402_);
    v_i_boxed_7415_ = leanh::lean_unbox_usize(v_i_7403_);
    leanh::lean_dec(v_i_7403_);
    v_res_7416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__3(v_pre_7397_, v_post_7398_, v_usedLetOnly_boxed_7411_, v_skipConstInApp_boxed_7412_, v_skipInstances_boxed_7413_, v_sz_boxed_7414_, v_i_boxed_7415_, v_bs_7404_, v___y_7405_, v___y_7406_, v___y_7407_, v___y_7408_, v___y_7409_);
    leanh::lean_dec(v___y_7409_);
    leanh::lean_dec_ref(v___y_7408_);
    leanh::lean_dec(v___y_7407_);
    leanh::lean_dec_ref(v___y_7406_);
    leanh::lean_dec(v___y_7405_);
    return v_res_7416_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2___boxed(
    mut v_pre_7417_: *mut leanh::LeanObject,
    mut v_post_7418_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7419_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7420_: *mut leanh::LeanObject,
    mut v_skipInstances_7421_: *mut leanh::LeanObject,
    mut v_e_7422_: *mut leanh::LeanObject,
    mut v_a_7423_: *mut leanh::LeanObject,
    mut v___y_7424_: *mut leanh::LeanObject,
    mut v___y_7425_: *mut leanh::LeanObject,
    mut v___y_7426_: *mut leanh::LeanObject,
    mut v___y_7427_: *mut leanh::LeanObject,
    mut v___y_7428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7429_: u8 = 0;
    let mut v_skipConstInApp_boxed_7430_: u8 = 0;
    let mut v_skipInstances_boxed_7431_: u8 = 0;
    let mut v_res_7432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7429_ = (leanh::lean_unbox(v_usedLetOnly_7419_) as u8);
    v_skipConstInApp_boxed_7430_ = (leanh::lean_unbox(v_skipConstInApp_7420_) as u8);
    v_skipInstances_boxed_7431_ = (leanh::lean_unbox(v_skipInstances_7421_) as u8);
    v_res_7432_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7417_, v_post_7418_, v_usedLetOnly_boxed_7429_, v_skipConstInApp_boxed_7430_, v_skipInstances_boxed_7431_, v_e_7422_, v_a_7423_, v___y_7424_, v___y_7425_, v___y_7426_, v___y_7427_);
    leanh::lean_dec(v___y_7427_);
    leanh::lean_dec_ref(v___y_7426_);
    leanh::lean_dec(v___y_7425_);
    leanh::lean_dec_ref(v___y_7424_);
    leanh::lean_dec(v_a_7423_);
    return v_res_7432_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6___boxed(
    mut v_pre_7433_: *mut leanh::LeanObject,
    mut v_post_7434_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7435_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7436_: *mut leanh::LeanObject,
    mut v_skipInstances_7437_: *mut leanh::LeanObject,
    mut v_fvars_7438_: *mut leanh::LeanObject,
    mut v_e_7439_: *mut leanh::LeanObject,
    mut v_a_7440_: *mut leanh::LeanObject,
    mut v___y_7441_: *mut leanh::LeanObject,
    mut v___y_7442_: *mut leanh::LeanObject,
    mut v___y_7443_: *mut leanh::LeanObject,
    mut v___y_7444_: *mut leanh::LeanObject,
    mut v___y_7445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7446_: u8 = 0;
    let mut v_skipConstInApp_boxed_7447_: u8 = 0;
    let mut v_skipInstances_boxed_7448_: u8 = 0;
    let mut v_res_7449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7446_ = (leanh::lean_unbox(v_usedLetOnly_7435_) as u8);
    v_skipConstInApp_boxed_7447_ = (leanh::lean_unbox(v_skipConstInApp_7436_) as u8);
    v_skipInstances_boxed_7448_ = (leanh::lean_unbox(v_skipInstances_7437_) as u8);
    v_res_7449_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6(v_pre_7433_, v_post_7434_, v_usedLetOnly_boxed_7446_, v_skipConstInApp_boxed_7447_, v_skipInstances_boxed_7448_, v_fvars_7438_, v_e_7439_, v_a_7440_, v___y_7441_, v___y_7442_, v___y_7443_, v___y_7444_);
    leanh::lean_dec(v___y_7444_);
    leanh::lean_dec_ref(v___y_7443_);
    leanh::lean_dec(v___y_7442_);
    leanh::lean_dec_ref(v___y_7441_);
    leanh::lean_dec(v_a_7440_);
    return v_res_7449_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7___boxed(
    mut v_pre_7450_: *mut leanh::LeanObject,
    mut v_post_7451_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7452_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7453_: *mut leanh::LeanObject,
    mut v_skipInstances_7454_: *mut leanh::LeanObject,
    mut v_fvars_7455_: *mut leanh::LeanObject,
    mut v_e_7456_: *mut leanh::LeanObject,
    mut v_a_7457_: *mut leanh::LeanObject,
    mut v___y_7458_: *mut leanh::LeanObject,
    mut v___y_7459_: *mut leanh::LeanObject,
    mut v___y_7460_: *mut leanh::LeanObject,
    mut v___y_7461_: *mut leanh::LeanObject,
    mut v___y_7462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7463_: u8 = 0;
    let mut v_skipConstInApp_boxed_7464_: u8 = 0;
    let mut v_skipInstances_boxed_7465_: u8 = 0;
    let mut v_res_7466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7463_ = (leanh::lean_unbox(v_usedLetOnly_7452_) as u8);
    v_skipConstInApp_boxed_7464_ = (leanh::lean_unbox(v_skipConstInApp_7453_) as u8);
    v_skipInstances_boxed_7465_ = (leanh::lean_unbox(v_skipInstances_7454_) as u8);
    v_res_7466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__7(v_pre_7450_, v_post_7451_, v_usedLetOnly_boxed_7463_, v_skipConstInApp_boxed_7464_, v_skipInstances_boxed_7465_, v_fvars_7455_, v_e_7456_, v_a_7457_, v___y_7458_, v___y_7459_, v___y_7460_, v___y_7461_);
    leanh::lean_dec(v___y_7461_);
    leanh::lean_dec_ref(v___y_7460_);
    leanh::lean_dec(v___y_7459_);
    leanh::lean_dec_ref(v___y_7458_);
    leanh::lean_dec(v_a_7457_);
    return v_res_7466_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8___boxed(
    mut v_pre_7467_: *mut leanh::LeanObject,
    mut v_post_7468_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7469_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7470_: *mut leanh::LeanObject,
    mut v_skipInstances_7471_: *mut leanh::LeanObject,
    mut v_fvars_7472_: *mut leanh::LeanObject,
    mut v_e_7473_: *mut leanh::LeanObject,
    mut v_a_7474_: *mut leanh::LeanObject,
    mut v___y_7475_: *mut leanh::LeanObject,
    mut v___y_7476_: *mut leanh::LeanObject,
    mut v___y_7477_: *mut leanh::LeanObject,
    mut v___y_7478_: *mut leanh::LeanObject,
    mut v___y_7479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7480_: u8 = 0;
    let mut v_skipConstInApp_boxed_7481_: u8 = 0;
    let mut v_skipInstances_boxed_7482_: u8 = 0;
    let mut v_res_7483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7480_ = (leanh::lean_unbox(v_usedLetOnly_7469_) as u8);
    v_skipConstInApp_boxed_7481_ = (leanh::lean_unbox(v_skipConstInApp_7470_) as u8);
    v_skipInstances_boxed_7482_ = (leanh::lean_unbox(v_skipInstances_7471_) as u8);
    v_res_7483_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8(v_pre_7467_, v_post_7468_, v_usedLetOnly_boxed_7480_, v_skipConstInApp_boxed_7481_, v_skipInstances_boxed_7482_, v_fvars_7472_, v_e_7473_, v_a_7474_, v___y_7475_, v___y_7476_, v___y_7477_, v___y_7478_);
    leanh::lean_dec(v___y_7478_);
    leanh::lean_dec_ref(v___y_7477_);
    leanh::lean_dec(v___y_7476_);
    leanh::lean_dec_ref(v___y_7475_);
    leanh::lean_dec(v_a_7474_);
    return v_res_7483_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg___boxed(
    mut v_upperBound_7484_: *mut leanh::LeanObject,
    mut v___x_7485_: *mut leanh::LeanObject,
    mut v_pre_7486_: *mut leanh::LeanObject,
    mut v_post_7487_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7488_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7489_: *mut leanh::LeanObject,
    mut v_skipInstances_7490_: *mut leanh::LeanObject,
    mut v_a_7491_: *mut leanh::LeanObject,
    mut v_b_7492_: *mut leanh::LeanObject,
    mut v___y_7493_: *mut leanh::LeanObject,
    mut v___y_7494_: *mut leanh::LeanObject,
    mut v___y_7495_: *mut leanh::LeanObject,
    mut v___y_7496_: *mut leanh::LeanObject,
    mut v___y_7497_: *mut leanh::LeanObject,
    mut v___y_7498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7499_: u8 = 0;
    let mut v_skipConstInApp_boxed_7500_: u8 = 0;
    let mut v_skipInstances_boxed_7501_: u8 = 0;
    let mut v_res_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7499_ = (leanh::lean_unbox(v_usedLetOnly_7488_) as u8);
    v_skipConstInApp_boxed_7500_ = (leanh::lean_unbox(v_skipConstInApp_7489_) as u8);
    v_skipInstances_boxed_7501_ = (leanh::lean_unbox(v_skipInstances_7490_) as u8);
    v_res_7502_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg(v_upperBound_7484_, v___x_7485_, v_pre_7486_, v_post_7487_, v_usedLetOnly_boxed_7499_, v_skipConstInApp_boxed_7500_, v_skipInstances_boxed_7501_, v_a_7491_, v_b_7492_, v___y_7493_, v___y_7494_, v___y_7495_, v___y_7496_, v___y_7497_);
    leanh::lean_dec(v___y_7497_);
    leanh::lean_dec_ref(v___y_7496_);
    leanh::lean_dec(v___y_7495_);
    leanh::lean_dec_ref(v___y_7494_);
    leanh::lean_dec(v___y_7493_);
    leanh::lean_dec_ref(v___x_7485_);
    leanh::lean_dec(v_upperBound_7484_);
    return v_res_7502_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__9___boxed(
    mut v_skipInstances_7503_: *mut leanh::LeanObject,
    mut v_pre_7504_: *mut leanh::LeanObject,
    mut v_post_7505_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7506_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7507_: *mut leanh::LeanObject,
    mut v_x_7508_: *mut leanh::LeanObject,
    mut v_x_7509_: *mut leanh::LeanObject,
    mut v_x_7510_: *mut leanh::LeanObject,
    mut v___y_7511_: *mut leanh::LeanObject,
    mut v___y_7512_: *mut leanh::LeanObject,
    mut v___y_7513_: *mut leanh::LeanObject,
    mut v___y_7514_: *mut leanh::LeanObject,
    mut v___y_7515_: *mut leanh::LeanObject,
    mut v___y_7516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipInstances_boxed_7517_: u8 = 0;
    let mut v_usedLetOnly_boxed_7518_: u8 = 0;
    let mut v_skipConstInApp_boxed_7519_: u8 = 0;
    let mut v_res_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_7517_ = (leanh::lean_unbox(v_skipInstances_7503_) as u8);
    v_usedLetOnly_boxed_7518_ = (leanh::lean_unbox(v_usedLetOnly_7506_) as u8);
    v_skipConstInApp_boxed_7519_ = (leanh::lean_unbox(v_skipConstInApp_7507_) as u8);
    v_res_7520_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__9(v_skipInstances_boxed_7517_, v_pre_7504_, v_post_7505_, v_usedLetOnly_boxed_7518_, v_skipConstInApp_boxed_7519_, v_x_7508_, v_x_7509_, v_x_7510_, v___y_7511_, v___y_7512_, v___y_7513_, v___y_7514_, v___y_7515_);
    leanh::lean_dec(v___y_7515_);
    leanh::lean_dec_ref(v___y_7514_);
    leanh::lean_dec(v___y_7513_);
    leanh::lean_dec_ref(v___y_7512_);
    leanh::lean_dec(v___y_7511_);
    return v_res_7520_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2(
    mut v_input_7521_: *mut leanh::LeanObject,
    mut v_pre_7522_: *mut leanh::LeanObject,
    mut v_post_7523_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7524_: u8,
    mut v_skipConstInApp_7525_: u8,
    mut v___y_7526_: *mut leanh::LeanObject,
    mut v___y_7527_: *mut leanh::LeanObject,
    mut v___y_7528_: *mut leanh::LeanObject,
    mut v___y_7529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: u8 = 0;
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7541_: u8 = 0;
    let mut v___x_7543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7545_: u8 = 0;
    let mut v_unused_7546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7531_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1___closed__2);
                v___x_7532_ = l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2___lam__0(leanh::lean_box(0), v___x_7531_, v___y_7526_, v___y_7527_, v___y_7528_, v___y_7529_);
                v_a_7533_ = leanh::lean_ctor_get(v___x_7532_, 0);
                leanh::lean_inc(v_a_7533_);
                leanh::lean_dec_ref(v___x_7532_);
                v___x_7534_ = 0;
                v___x_7535_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2(v_pre_7522_, v_post_7523_, v_usedLetOnly_7524_, v_skipConstInApp_7525_, v___x_7534_, v_input_7521_, v_a_7533_, v___y_7526_, v___y_7527_, v___y_7528_, v___y_7529_);
                if leanh::lean_obj_tag(v___x_7535_) == 0 {
                    v_a_7536_ = leanh::lean_ctor_get(v___x_7535_, 0);
                    leanh::lean_inc(v_a_7536_);
                    leanh::lean_dec_ref_known(v___x_7535_, 1);
                    v___x_7537_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_7537_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7537_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7537_, 2, v_a_7533_);
                    v___x_7538_ = l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2___lam__0(leanh::lean_box(0), v___x_7537_, v___y_7526_, v___y_7527_, v___y_7528_, v___y_7529_);
                    v_isSharedCheck_7545_ = (!leanh::lean_is_exclusive(v___x_7538_)) as u8;
                    if v_isSharedCheck_7545_ == 0 {
                        v_unused_7546_ = leanh::lean_ctor_get(v___x_7538_, 0);
                        leanh::lean_dec(v_unused_7546_);
                        v___x_7540_ = v___x_7538_;
                        v_isShared_7541_ = v_isSharedCheck_7545_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7538_);
                        v___x_7540_ = leanh::lean_box(0);
                        v_isShared_7541_ = v_isSharedCheck_7545_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7533_);
                    return v___x_7535_;
                }
            }
            1 => {
                if v_isShared_7541_ == 0 {
                    leanh::lean_ctor_set(v___x_7540_, 0, v_a_7536_);
                    v___x_7543_ = v___x_7540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7544_, 0, v_a_7536_);
                    v___x_7543_ = v_reuseFailAlloc_7544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2___boxed(
    mut v_input_7547_: *mut leanh::LeanObject,
    mut v_pre_7548_: *mut leanh::LeanObject,
    mut v_post_7549_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7550_: *mut leanh::LeanObject,
    mut v_skipConstInApp_7551_: *mut leanh::LeanObject,
    mut v___y_7552_: *mut leanh::LeanObject,
    mut v___y_7553_: *mut leanh::LeanObject,
    mut v___y_7554_: *mut leanh::LeanObject,
    mut v___y_7555_: *mut leanh::LeanObject,
    mut v___y_7556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7557_: u8 = 0;
    let mut v_skipConstInApp_boxed_7558_: u8 = 0;
    let mut v_res_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7557_ = (leanh::lean_unbox(v_usedLetOnly_7550_) as u8);
    v_skipConstInApp_boxed_7558_ = (leanh::lean_unbox(v_skipConstInApp_7551_) as u8);
    v_res_7559_ = l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2(
        v_input_7547_,
        v_pre_7548_,
        v_post_7549_,
        v_usedLetOnly_boxed_7557_,
        v_skipConstInApp_boxed_7558_,
        v___y_7552_,
        v___y_7553_,
        v___y_7554_,
        v___y_7555_,
    );
    leanh::lean_dec(v___y_7555_);
    leanh::lean_dec_ref(v___y_7554_);
    leanh::lean_dec(v___y_7553_);
    leanh::lean_dec_ref(v___y_7552_);
    return v_res_7559_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__1() -> u64 {
    let mut v___x_7566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: u64 = 0;
    v___x_7566_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
    v___x_7567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_7566_);
    return v___x_7567_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7568_: u64 = 0;
    let mut v___x_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7568_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__1_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__1,
    );
    v___x_7569_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
    v___x_7570_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_7570_, 0, v___x_7569_);
    leanh::lean_ctor_set_uint64(
        v___x_7570_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_7568_,
    );
    return v___x_7570_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7571_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_7571_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7572_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__3_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__3,
    );
    v___x_7573_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7573_, 0, v___x_7572_);
    return v___x_7573_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7574_ = leanh::lean_box(1);
    v___x_7575_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4);
    v___x_7576_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4,
    );
    v___x_7577_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_7577_, 0, v___x_7576_);
    leanh::lean_ctor_set(v___x_7577_, 1, v___x_7575_);
    leanh::lean_ctor_set(v___x_7577_, 2, v___x_7574_);
    return v___x_7577_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_7580_: u8 = 0;
    let mut v___x_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7586_: u8 = 0;
    let mut v___x_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7580_ = 1;
    v___x_7581_ = leanh::lean_unsigned_to_nat(0);
    v___x_7582_ = leanh::lean_box(0);
    v___x_7583_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
    v___x_7584_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__5_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5,
    );
    v___x_7585_ = leanh::lean_box(1);
    v___x_7586_ = 0;
    v___x_7587_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__2_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2,
    );
    v___x_7588_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_7588_, 0, v___x_7587_);
    leanh::lean_ctor_set(v___x_7588_, 1, v___x_7585_);
    leanh::lean_ctor_set(v___x_7588_, 2, v___x_7584_);
    leanh::lean_ctor_set(v___x_7588_, 3, v___x_7583_);
    leanh::lean_ctor_set(v___x_7588_, 4, v___x_7582_);
    leanh::lean_ctor_set(v___x_7588_, 5, v___x_7581_);
    leanh::lean_ctor_set(v___x_7588_, 6, v___x_7582_);
    leanh::lean_ctor_set_uint8(
        v___x_7588_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_7586_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_7588_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v___x_7586_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_7588_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v___x_7586_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_7588_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v___x_7580_,
    );
    return v___x_7588_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7589_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4,
    );
    v___x_7590_ = leanh::lean_unsigned_to_nat(0);
    v___x_7591_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_7591_, 0, v___x_7590_);
    leanh::lean_ctor_set(v___x_7591_, 1, v___x_7590_);
    leanh::lean_ctor_set(v___x_7591_, 2, v___x_7590_);
    leanh::lean_ctor_set(v___x_7591_, 3, v___x_7590_);
    leanh::lean_ctor_set(v___x_7591_, 4, v___x_7589_);
    leanh::lean_ctor_set(v___x_7591_, 5, v___x_7589_);
    leanh::lean_ctor_set(v___x_7591_, 6, v___x_7589_);
    leanh::lean_ctor_set(v___x_7591_, 7, v___x_7589_);
    leanh::lean_ctor_set(v___x_7591_, 8, v___x_7589_);
    leanh::lean_ctor_set(v___x_7591_, 9, v___x_7589_);
    return v___x_7591_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_7592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7592_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4,
    );
    v___x_7593_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_7593_, 0, v___x_7592_);
    leanh::lean_ctor_set(v___x_7593_, 1, v___x_7592_);
    leanh::lean_ctor_set(v___x_7593_, 2, v___x_7592_);
    leanh::lean_ctor_set(v___x_7593_, 3, v___x_7592_);
    leanh::lean_ctor_set(v___x_7593_, 4, v___x_7592_);
    leanh::lean_ctor_set(v___x_7593_, 5, v___x_7592_);
    return v___x_7593_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7594_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__4_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4,
    );
    v___x_7595_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_7595_, 0, v___x_7594_);
    leanh::lean_ctor_set(v___x_7595_, 1, v___x_7594_);
    leanh::lean_ctor_set(v___x_7595_, 2, v___x_7594_);
    leanh::lean_ctor_set(v___x_7595_, 3, v___x_7594_);
    leanh::lean_ctor_set(v___x_7595_, 4, v___x_7594_);
    return v___x_7595_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7596_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__10_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__10,
    );
    v___x_7597_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__4);
    v___x_7598_ = leanh::lean_box(1);
    v___x_7599_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__9_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__9,
    );
    v___x_7600_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__8_once),
        _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__8,
    );
    v___x_7601_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_7601_, 0, v___x_7600_);
    leanh::lean_ctor_set(v___x_7601_, 1, v___x_7599_);
    leanh::lean_ctor_set(v___x_7601_, 2, v___x_7598_);
    leanh::lean_ctor_set(v___x_7601_, 3, v___x_7597_);
    leanh::lean_ctor_set(v___x_7601_, 4, v___x_7596_);
    return v___x_7601_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers(
    mut v_e_7604_: *mut leanh::LeanObject,
    mut v_a_7605_: *mut leanh::LeanObject,
    mut v_a_7606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7608_: u8 = 0;
    let mut v___x_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7618_: u8 = 0;
    let mut v___x_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7608_ = 0;
                v___x_7609_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__7_once),
                    _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__7,
                );
                v___x_7610_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inlineMatchers___closed__11_once),
                    _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11,
                );
                v___x_7611_ = lean_st_mk_ref(v___x_7610_);
                v___f_7612_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
                v___f_7613_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
                v___x_7614_ =
                    l_Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2(
                        v_e_7604_,
                        v___f_7613_,
                        v___f_7612_,
                        v___x_7608_,
                        v___x_7608_,
                        v___x_7609_,
                        v___x_7611_,
                        v_a_7605_,
                        v_a_7606_,
                    );
                if leanh::lean_obj_tag(v___x_7614_) == 0 {
                    v_a_7615_ = leanh::lean_ctor_get(v___x_7614_, 0);
                    v_isSharedCheck_7623_ = (!leanh::lean_is_exclusive(v___x_7614_)) as u8;
                    if v_isSharedCheck_7623_ == 0 {
                        v___x_7617_ = v___x_7614_;
                        v_isShared_7618_ = v_isSharedCheck_7623_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7615_);
                        leanh::lean_dec(v___x_7614_);
                        v___x_7617_ = leanh::lean_box(0);
                        v_isShared_7618_ = v_isSharedCheck_7623_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_7611_);
                    return v___x_7614_;
                }
            }
            1 => {
                v___x_7619_ = lean_st_ref_get(v___x_7611_);
                leanh::lean_dec(v___x_7611_);
                leanh::lean_dec(v___x_7619_);
                if v_isShared_7618_ == 0 {
                    v___x_7621_ = v___x_7617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7622_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7622_, 0, v_a_7615_);
                    v___x_7621_ = v_reuseFailAlloc_7622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_inlineMatchers___boxed(
    mut v_e_7624_: *mut leanh::LeanObject,
    mut v_a_7625_: *mut leanh::LeanObject,
    mut v_a_7626_: *mut leanh::LeanObject,
    mut v_a_7627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7628_ = l_Lean_Compiler_LCNF_inlineMatchers(v_e_7624_, v_a_7625_, v_a_7626_);
    leanh::lean_dec(v_a_7626_);
    leanh::lean_dec_ref(v_a_7625_);
    return v_res_7628_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5(
    mut v_upperBound_7629_: *mut leanh::LeanObject,
    mut v___x_7630_: *mut leanh::LeanObject,
    mut v_pre_7631_: *mut leanh::LeanObject,
    mut v_post_7632_: *mut leanh::LeanObject,
    mut v_usedLetOnly_7633_: u8,
    mut v_skipConstInApp_7634_: u8,
    mut v_skipInstances_7635_: u8,
    mut v___x_7636_: *mut leanh::LeanObject,
    mut v_inst_7637_: *mut leanh::LeanObject,
    mut v_R_7638_: *mut leanh::LeanObject,
    mut v_a_7639_: *mut leanh::LeanObject,
    mut v_b_7640_: *mut leanh::LeanObject,
    mut v_c_7641_: *mut leanh::LeanObject,
    mut v___y_7642_: *mut leanh::LeanObject,
    mut v___y_7643_: *mut leanh::LeanObject,
    mut v___y_7644_: *mut leanh::LeanObject,
    mut v___y_7645_: *mut leanh::LeanObject,
    mut v___y_7646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___redArg(v_upperBound_7629_, v___x_7630_, v_pre_7631_, v_post_7632_, v_usedLetOnly_7633_, v_skipConstInApp_7634_, v_skipInstances_7635_, v_a_7639_, v_b_7640_, v___y_7642_, v___y_7643_, v___y_7644_, v___y_7645_, v___y_7646_);
    return v___x_7648_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_upperBound_7649_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_7650_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_pre_7651_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_post_7652_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_usedLetOnly_7653_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_skipConstInApp_7654_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_skipInstances_7655_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_7656_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_7657_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_R_7658_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_7659_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_b_7660_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_c_7661_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7662_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7663_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7664_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7665_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_7666_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_7667_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_usedLetOnly_boxed_7668_: u8 = 0;
    let mut v_skipConstInApp_boxed_7669_: u8 = 0;
    let mut v_skipInstances_boxed_7670_: u8 = 0;
    let mut v_res_7671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7668_ = (leanh::lean_unbox(v_usedLetOnly_7653_) as u8);
    v_skipConstInApp_boxed_7669_ = (leanh::lean_unbox(v_skipConstInApp_7654_) as u8);
    v_skipInstances_boxed_7670_ = (leanh::lean_unbox(v_skipInstances_7655_) as u8);
    v_res_7671_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__5(v_upperBound_7649_, v___x_7650_, v_pre_7651_, v_post_7652_, v_usedLetOnly_boxed_7668_, v_skipConstInApp_boxed_7669_, v_skipInstances_boxed_7670_, v___x_7656_, v_inst_7657_, v_R_7658_, v_a_7659_, v_b_7660_, v_c_7661_, v___y_7662_, v___y_7663_, v___y_7664_, v___y_7665_, v___y_7666_);
    leanh::lean_dec(v___y_7666_);
    leanh::lean_dec_ref(v___y_7665_);
    leanh::lean_dec(v___y_7664_);
    leanh::lean_dec_ref(v___y_7663_);
    leanh::lean_dec(v___y_7662_);
    leanh::lean_dec(v___x_7656_);
    leanh::lean_dec_ref(v___x_7650_);
    leanh::lean_dec(v_upperBound_7649_);
    return v_res_7671_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7(
    mut v_00_u03b1_7672_: *mut leanh::LeanObject,
    mut v_name_7673_: *mut leanh::LeanObject,
    mut v_bi_7674_: u8,
    mut v_type_7675_: *mut leanh::LeanObject,
    mut v_k_7676_: *mut leanh::LeanObject,
    mut v_kind_7677_: u8,
    mut v___y_7678_: *mut leanh::LeanObject,
    mut v___y_7679_: *mut leanh::LeanObject,
    mut v___y_7680_: *mut leanh::LeanObject,
    mut v___y_7681_: *mut leanh::LeanObject,
    mut v___y_7682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7684_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___redArg(v_name_7673_, v_bi_7674_, v_type_7675_, v_k_7676_, v_kind_7677_, v___y_7678_, v___y_7679_, v___y_7680_, v___y_7681_, v___y_7682_);
    return v___x_7684_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7___boxed(
    mut v_00_u03b1_7685_: *mut leanh::LeanObject,
    mut v_name_7686_: *mut leanh::LeanObject,
    mut v_bi_7687_: *mut leanh::LeanObject,
    mut v_type_7688_: *mut leanh::LeanObject,
    mut v_k_7689_: *mut leanh::LeanObject,
    mut v_kind_7690_: *mut leanh::LeanObject,
    mut v___y_7691_: *mut leanh::LeanObject,
    mut v___y_7692_: *mut leanh::LeanObject,
    mut v___y_7693_: *mut leanh::LeanObject,
    mut v___y_7694_: *mut leanh::LeanObject,
    mut v___y_7695_: *mut leanh::LeanObject,
    mut v___y_7696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_7697_: u8 = 0;
    let mut v_kind_boxed_7698_: u8 = 0;
    let mut v_res_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_7697_ = (leanh::lean_unbox(v_bi_7687_) as u8);
    v_kind_boxed_7698_ = (leanh::lean_unbox(v_kind_7690_) as u8);
    v_res_7699_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__6_spec__7(v_00_u03b1_7685_, v_name_7686_, v_bi_boxed_7697_, v_type_7688_, v_k_7689_, v_kind_boxed_7698_, v___y_7691_, v___y_7692_, v___y_7693_, v___y_7694_, v___y_7695_);
    leanh::lean_dec(v___y_7695_);
    leanh::lean_dec_ref(v___y_7694_);
    leanh::lean_dec(v___y_7693_);
    leanh::lean_dec_ref(v___y_7692_);
    leanh::lean_dec(v___y_7691_);
    return v_res_7699_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10(
    mut v_00_u03b1_7700_: *mut leanh::LeanObject,
    mut v_name_7701_: *mut leanh::LeanObject,
    mut v_type_7702_: *mut leanh::LeanObject,
    mut v_val_7703_: *mut leanh::LeanObject,
    mut v_k_7704_: *mut leanh::LeanObject,
    mut v_nondep_7705_: u8,
    mut v_kind_7706_: u8,
    mut v___y_7707_: *mut leanh::LeanObject,
    mut v___y_7708_: *mut leanh::LeanObject,
    mut v___y_7709_: *mut leanh::LeanObject,
    mut v___y_7710_: *mut leanh::LeanObject,
    mut v___y_7711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7713_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10___redArg(v_name_7701_, v_type_7702_, v_val_7703_, v_k_7704_, v_nondep_7705_, v_kind_7706_, v___y_7707_, v___y_7708_, v___y_7709_, v___y_7710_, v___y_7711_);
    return v___x_7713_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10___boxed(
    mut v_00_u03b1_7714_: *mut leanh::LeanObject,
    mut v_name_7715_: *mut leanh::LeanObject,
    mut v_type_7716_: *mut leanh::LeanObject,
    mut v_val_7717_: *mut leanh::LeanObject,
    mut v_k_7718_: *mut leanh::LeanObject,
    mut v_nondep_7719_: *mut leanh::LeanObject,
    mut v_kind_7720_: *mut leanh::LeanObject,
    mut v___y_7721_: *mut leanh::LeanObject,
    mut v___y_7722_: *mut leanh::LeanObject,
    mut v___y_7723_: *mut leanh::LeanObject,
    mut v___y_7724_: *mut leanh::LeanObject,
    mut v___y_7725_: *mut leanh::LeanObject,
    mut v___y_7726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_7727_: u8 = 0;
    let mut v_kind_boxed_7728_: u8 = 0;
    let mut v_res_7729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_7727_ = (leanh::lean_unbox(v_nondep_7719_) as u8);
    v_kind_boxed_7728_ = (leanh::lean_unbox(v_kind_7720_) as u8);
    v_res_7729_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__8_spec__10(v_00_u03b1_7714_, v_name_7715_, v_type_7716_, v_val_7717_, v_k_7718_, v_nondep_boxed_7727_, v_kind_boxed_7728_, v___y_7721_, v___y_7722_, v___y_7723_, v___y_7724_, v___y_7725_);
    leanh::lean_dec(v___y_7725_);
    leanh::lean_dec_ref(v___y_7724_);
    leanh::lean_dec(v___y_7723_);
    leanh::lean_dec_ref(v___y_7722_);
    leanh::lean_dec(v___y_7721_);
    return v_res_7729_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13(
    mut v_00_u03b1_7730_: *mut leanh::LeanObject,
    mut v_ref_7731_: *mut leanh::LeanObject,
    mut v___y_7732_: *mut leanh::LeanObject,
    mut v___y_7733_: *mut leanh::LeanObject,
    mut v___y_7734_: *mut leanh::LeanObject,
    mut v___y_7735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7737_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13___redArg(v_ref_7731_);
    return v___x_7737_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13___boxed(
    mut v_00_u03b1_7738_: *mut leanh::LeanObject,
    mut v_ref_7739_: *mut leanh::LeanObject,
    mut v___y_7740_: *mut leanh::LeanObject,
    mut v___y_7741_: *mut leanh::LeanObject,
    mut v___y_7742_: *mut leanh::LeanObject,
    mut v___y_7743_: *mut leanh::LeanObject,
    mut v___y_7744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7745_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10_spec__13(v_00_u03b1_7738_, v_ref_7739_, v___y_7740_, v___y_7741_, v___y_7742_, v___y_7743_);
    leanh::lean_dec(v___y_7743_);
    leanh::lean_dec_ref(v___y_7742_);
    leanh::lean_dec(v___y_7741_);
    leanh::lean_dec_ref(v___y_7740_);
    return v_res_7745_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10(
    mut v_00_u03b1_7746_: *mut leanh::LeanObject,
    mut v_x_7747_: *mut leanh::LeanObject,
    mut v___y_7748_: *mut leanh::LeanObject,
    mut v___y_7749_: *mut leanh::LeanObject,
    mut v___y_7750_: *mut leanh::LeanObject,
    mut v___y_7751_: *mut leanh::LeanObject,
    mut v___y_7752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7754_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10___redArg(v_x_7747_, v___y_7748_, v___y_7749_, v___y_7750_, v___y_7751_, v___y_7752_);
    return v___x_7754_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10___boxed(
    mut v_00_u03b1_7755_: *mut leanh::LeanObject,
    mut v_x_7756_: *mut leanh::LeanObject,
    mut v___y_7757_: *mut leanh::LeanObject,
    mut v___y_7758_: *mut leanh::LeanObject,
    mut v___y_7759_: *mut leanh::LeanObject,
    mut v___y_7760_: *mut leanh::LeanObject,
    mut v___y_7761_: *mut leanh::LeanObject,
    mut v___y_7762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7763_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Compiler_LCNF_inlineMatchers_spec__2_spec__2_spec__10(v_00_u03b1_7755_, v_x_7756_, v___y_7757_, v___y_7758_, v___y_7759_, v___y_7760_, v___y_7761_);
    leanh::lean_dec(v___y_7761_);
    leanh::lean_dec_ref(v___y_7760_);
    leanh::lean_dec(v___y_7759_);
    leanh::lean_dec_ref(v___y_7758_);
    leanh::lean_dec(v___y_7757_);
    return v_res_7763_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(
    mut v_e_7764_: *mut leanh::LeanObject,
    mut v___y_7765_: *mut leanh::LeanObject,
    mut v___y_7766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_7768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_7769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7774_: u8 = 0;
    let mut v___x_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7780_: u8 = 0;
    let mut v___x_7781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_7764_) == 4 {
                    v_declName_7768_ = leanh::lean_ctor_get(v_e_7764_, 0);
                    v_us_7769_ = leanh::lean_ctor_get(v_e_7764_, 1);
                    v___x_7770_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_7768_);
                    if leanh::lean_obj_tag(v___x_7770_) == 1 {
                        leanh::lean_inc(v_us_7769_);
                        leanh::lean_dec_ref_known(v_e_7764_, 2);
                        v_val_7771_ = leanh::lean_ctor_get(v___x_7770_, 0);
                        v_isSharedCheck_7780_ =
                            (!leanh::lean_is_exclusive(v___x_7770_)) as u8;
                        if v_isSharedCheck_7780_ == 0 {
                            v___x_7773_ = v___x_7770_;
                            v_isShared_7774_ = v_isSharedCheck_7780_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_7771_);
                            leanh::lean_dec(v___x_7770_);
                            v___x_7773_ = leanh::lean_box(0);
                            v_isShared_7774_ = v_isSharedCheck_7780_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_7770_);
                        v___x_7781_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7781_, 0, v_e_7764_);
                        v___x_7782_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7782_, 0, v___x_7781_);
                        return v___x_7782_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7764_);
                    v___x_7783_ = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
                    v___x_7784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7784_, 0, v___x_7783_);
                    return v___x_7784_;
                }
            }
            1 => {
                v___x_7775_ = l_Lean_Expr_const___override(v_val_7771_, v_us_7769_);
                if v_isShared_7774_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7773_, 0);
                    leanh::lean_ctor_set(v___x_7773_, 0, v___x_7775_);
                    v___x_7777_ = v___x_7773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7779_, 0, v___x_7775_);
                    v___x_7777_ = v_reuseFailAlloc_7779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7778_, 0, v___x_7777_);
                return v___x_7778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed(
    mut v_e_7785_: *mut leanh::LeanObject,
    mut v___y_7786_: *mut leanh::LeanObject,
    mut v___y_7787_: *mut leanh::LeanObject,
    mut v___y_7788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7789_ =
        l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(
            v_e_7785_,
            v___y_7786_,
            v___y_7787_,
        );
    leanh::lean_dec(v___y_7787_);
    leanh::lean_dec_ref(v___y_7786_);
    return v_res_7789_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(
    mut v_value_7791_: *mut leanh::LeanObject,
    mut v_a_7792_: *mut leanh::LeanObject,
    mut v_a_7793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7795_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0;
    v___f_7796_ = l_Lean_Compiler_LCNF_macroInline___closed__0;
    v___x_7797_ = l_Lean_Core_transform___at___00Lean_Compiler_LCNF_macroInline_spec__1(
        v_value_7791_,
        v___f_7795_,
        v___f_7796_,
        v_a_7792_,
        v_a_7793_,
    );
    return v___x_7797_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___boxed(
    mut v_value_7798_: *mut leanh::LeanObject,
    mut v_a_7799_: *mut leanh::LeanObject,
    mut v_a_7800_: *mut leanh::LeanObject,
    mut v_a_7801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7802_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(
        v_value_7798_,
        v_a_7799_,
        v_a_7800_,
    );
    leanh::lean_dec(v_a_7800_);
    leanh::lean_dec_ref(v_a_7799_);
    return v_res_7802_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(
    mut v_declName_7803_: *mut leanh::LeanObject,
    mut v_a_7804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: u8 = 0;
    let mut v___x_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7806_ = lean_st_ref_get(v_a_7804_);
    v_env_7807_ = leanh::lean_ctor_get(v___x_7806_, 0);
    leanh::lean_inc_ref_n(v_env_7807_, 2);
    leanh::lean_dec(v___x_7806_);
    leanh::lean_inc(v_declName_7803_);
    v___x_7808_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_7803_);
    v___x_7809_ = 0;
    v___x_7810_ = l_Lean_Environment_find_x3f(v_env_7807_, v___x_7808_, v___x_7809_);
    if leanh::lean_obj_tag(v___x_7810_) == 0 {
        let mut v___x_7811_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7812_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7811_ = l_Lean_Environment_find_x3f(v_env_7807_, v_declName_7803_, v___x_7809_);
        v___x_7812_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7812_, 0, v___x_7811_);
        return v___x_7812_;
    } else {
        let mut v___x_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_7807_);
        leanh::lean_dec(v_declName_7803_);
        v___x_7813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7813_, 0, v___x_7810_);
        return v___x_7813_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(
    mut v_declName_7814_: *mut leanh::LeanObject,
    mut v_a_7815_: *mut leanh::LeanObject,
    mut v_a_7816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7817_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_7814_, v_a_7815_);
    leanh::lean_dec(v_a_7815_);
    return v_res_7817_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclInfo_x3f(
    mut v_declName_7818_: *mut leanh::LeanObject,
    mut v_a_7819_: *mut leanh::LeanObject,
    mut v_a_7820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7822_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_7818_, v_a_7820_);
    return v___x_7822_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(
    mut v_declName_7823_: *mut leanh::LeanObject,
    mut v_a_7824_: *mut leanh::LeanObject,
    mut v_a_7825_: *mut leanh::LeanObject,
    mut v_a_7826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7827_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f(v_declName_7823_, v_a_7824_, v_a_7825_);
    leanh::lean_dec(v_a_7825_);
    leanh::lean_dec_ref(v_a_7824_);
    return v_res_7827_;
}
pub unsafe fn l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(
    mut v_declName_7828_: *mut leanh::LeanObject,
    mut v_a_7829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: u8 = 0;
    let mut v___x_7834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7838_: u8 = 0;
    let mut v___x_7839_: u8 = 0;
    let mut v___y_7841_: u8 = 0;
    let mut v___x_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7850_: u8 = 0;
    let mut v___x_7851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7855_: u8 = 0;
    let mut v_unused_7856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: u8 = 0;
    let mut v___x_7858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7862_: u8 = 0;
    let mut v___x_7863_: u8 = 0;
    let mut v___x_7864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7831_ = lean_st_ref_get(v_a_7829_);
                v_env_7832_ = leanh::lean_ctor_get(v___x_7831_, 0);
                leanh::lean_inc_ref_n(v_env_7832_, 2);
                leanh::lean_dec(v___x_7831_);
                v___x_7833_ = 0;
                leanh::lean_inc(v_declName_7828_);
                v___x_7834_ =
                    l_Lean_Environment_find_x3f(v_env_7832_, v_declName_7828_, v___x_7833_);
                if leanh::lean_obj_tag(v___x_7834_) == 1 {
                    v_val_7835_ = leanh::lean_ctor_get(v___x_7834_, 0);
                    v_isSharedCheck_7862_ = (!leanh::lean_is_exclusive(v___x_7834_)) as u8;
                    if v_isSharedCheck_7862_ == 0 {
                        v___x_7837_ = v___x_7834_;
                        v_isShared_7838_ = v_isSharedCheck_7862_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7835_);
                        leanh::lean_dec(v___x_7834_);
                        v___x_7837_ = leanh::lean_box(0);
                        v_isShared_7838_ = v_isSharedCheck_7862_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_7834_);
                    leanh::lean_dec_ref(v_env_7832_);
                    leanh::lean_dec(v_declName_7828_);
                    v___x_7863_ = 1;
                    v___x_7864_ = leanh::lean_box((v___x_7863_) as usize);
                    v___x_7865_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7865_, 0, v___x_7864_);
                    return v___x_7865_;
                }
            }
            1 => {
                v___x_7839_ = l_Lean_ConstantInfo_isUnsafe(v_val_7835_);
                if v___x_7839_ == 0 {
                    v___x_7857_ = 1;
                    if leanh::lean_obj_tag(v_val_7835_) == 3 {
                        leanh::lean_dec_ref_known(v_val_7835_, 1);
                        v___y_7841_ = v___x_7857_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_7835_);
                        if v___x_7839_ == 0 {
                            leanh::lean_del_object(v___x_7837_);
                            leanh::lean_dec_ref(v_env_7832_);
                            leanh::lean_dec(v_declName_7828_);
                            v___x_7858_ = leanh::lean_box((v___x_7857_) as usize);
                            v___x_7859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_7859_, 0, v___x_7858_);
                            return v___x_7859_;
                        } else {
                            v___y_7841_ = v___x_7839_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7837_);
                    leanh::lean_dec(v_val_7835_);
                    leanh::lean_dec_ref(v_env_7832_);
                    leanh::lean_dec(v_declName_7828_);
                    v___x_7860_ = leanh::lean_box((v___x_7833_) as usize);
                    v___x_7861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7861_, 0, v___x_7860_);
                    return v___x_7861_;
                }
            }
            2 => {
                v___x_7842_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_7828_);
                v___x_7843_ = l_Lean_Environment_find_x3f(v_env_7832_, v___x_7842_, v___x_7839_);
                if leanh::lean_obj_tag(v___x_7843_) == 0 {
                    v___x_7844_ = leanh::lean_box((v___y_7841_) as usize);
                    if v_isShared_7838_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_7837_, 0);
                        leanh::lean_ctor_set(v___x_7837_, 0, v___x_7844_);
                        v___x_7846_ = v___x_7837_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7847_, 0, v___x_7844_);
                        v___x_7846_ = v_reuseFailAlloc_7847_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7837_);
                    v_isSharedCheck_7855_ = (!leanh::lean_is_exclusive(v___x_7843_)) as u8;
                    if v_isSharedCheck_7855_ == 0 {
                        v_unused_7856_ = leanh::lean_ctor_get(v___x_7843_, 0);
                        leanh::lean_dec(v_unused_7856_);
                        v___x_7849_ = v___x_7843_;
                        v_isShared_7850_ = v_isSharedCheck_7855_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7843_);
                        v___x_7849_ = leanh::lean_box(0);
                        v_isShared_7850_ = v_isSharedCheck_7855_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_7846_;
            }
            4 => {
                v___x_7851_ = leanh::lean_box((v___x_7839_) as usize);
                if v_isShared_7850_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7849_, 0);
                    leanh::lean_ctor_set(v___x_7849_, 0, v___x_7851_);
                    v___x_7853_ = v___x_7849_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7854_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7854_, 0, v___x_7851_);
                    v___x_7853_ = v_reuseFailAlloc_7854_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(
    mut v_declName_7866_: *mut leanh::LeanObject,
    mut v_a_7867_: *mut leanh::LeanObject,
    mut v_a_7868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7869_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_7866_, v_a_7867_);
    leanh::lean_dec(v_a_7867_);
    return v_res_7869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_declIsNotUnsafe(
    mut v_declName_7870_: *mut leanh::LeanObject,
    mut v_a_7871_: *mut leanh::LeanObject,
    mut v_a_7872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7874_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_7870_, v_a_7872_);
    return v___x_7874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(
    mut v_declName_7875_: *mut leanh::LeanObject,
    mut v_a_7876_: *mut leanh::LeanObject,
    mut v_a_7877_: *mut leanh::LeanObject,
    mut v_a_7878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7879_ = l_Lean_Compiler_LCNF_declIsNotUnsafe(v_declName_7875_, v_a_7876_, v_a_7877_);
    leanh::lean_dec(v_a_7877_);
    leanh::lean_dec_ref(v_a_7876_);
    return v_res_7879_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(
    mut v_opts_7880_: *mut leanh::LeanObject,
    mut v_opt_7881_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_7883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_7884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_7882_ = leanh::lean_ctor_get(v_opt_7881_, 0);
    v_defValue_7883_ = leanh::lean_ctor_get(v_opt_7881_, 1);
    v_map_7884_ = leanh::lean_ctor_get(v_opts_7880_, 0);
    v___x_7885_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_7884_,
            v_name_7882_,
        );
    if leanh::lean_obj_tag(v___x_7885_) == 0 {
        let mut v___x_7886_: u8 = 0;
        v___x_7886_ = (leanh::lean_unbox(v_defValue_7883_) as u8);
        return v___x_7886_;
    } else {
        let mut v_val_7887_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_7887_ = leanh::lean_ctor_get(v___x_7885_, 0);
        leanh::lean_inc(v_val_7887_);
        leanh::lean_dec_ref_known(v___x_7885_, 1);
        if leanh::lean_obj_tag(v_val_7887_) == 1 {
            let mut v_v_7888_: u8 = 0;
            v_v_7888_ = leanh::lean_ctor_get_uint8(v_val_7887_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_7887_, 0);
            return v_v_7888_;
        } else {
            let mut v___x_7889_: u8 = 0;
            leanh::lean_dec(v_val_7887_);
            v___x_7889_ = (leanh::lean_unbox(v_defValue_7883_) as u8);
            return v___x_7889_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(
    mut v_opts_7890_: *mut leanh::LeanObject,
    mut v_opt_7891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7892_: u8 = 0;
    let mut v_r_7893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7892_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_opts_7890_, v_opt_7891_);
    leanh::lean_dec_ref(v_opt_7891_);
    leanh::lean_dec_ref(v_opts_7890_);
    v_r_7893_ = leanh::lean_box((v_res_7892_) as usize);
    return v_r_7893_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(
    mut v_msg_7894_: *mut leanh::LeanObject,
    mut v___y_7895_: *mut leanh::LeanObject,
    mut v___y_7896_: *mut leanh::LeanObject,
    mut v___y_7897_: *mut leanh::LeanObject,
    mut v___y_7898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_7900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7908_: u8 = 0;
    let mut v_env_7909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7913_: u8 = 0;
    let mut v___x_7914_: u8 = 0;
    let mut v___x_7915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7925_: u8 = 0;
    let mut v_unused_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7927_: u8 = 0;
    let mut v_a_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7931_: u8 = 0;
    let mut v___x_7933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_7900_ = leanh::lean_ctor_get(v___y_7897_, 2);
                v_ref_7901_ = leanh::lean_ctor_get(v___y_7897_, 5);
                v___x_7902_ = lean_st_ref_get(v___y_7898_);
                v___x_7903_ = lean_st_ref_get(v___y_7896_);
                v___x_7904_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_7895_);
                if leanh::lean_obj_tag(v___x_7904_) == 0 {
                    v_a_7905_ = leanh::lean_ctor_get(v___x_7904_, 0);
                    v_isSharedCheck_7927_ = (!leanh::lean_is_exclusive(v___x_7904_)) as u8;
                    if v_isSharedCheck_7927_ == 0 {
                        v___x_7907_ = v___x_7904_;
                        v_isShared_7908_ = v_isSharedCheck_7927_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7905_);
                        leanh::lean_dec(v___x_7904_);
                        v___x_7907_ = leanh::lean_box(0);
                        v_isShared_7908_ = v_isSharedCheck_7927_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_7903_);
                    leanh::lean_dec(v___x_7902_);
                    leanh::lean_dec_ref(v_msg_7894_);
                    v_a_7928_ = leanh::lean_ctor_get(v___x_7904_, 0);
                    v_isSharedCheck_7935_ = (!leanh::lean_is_exclusive(v___x_7904_)) as u8;
                    if v_isSharedCheck_7935_ == 0 {
                        v___x_7930_ = v___x_7904_;
                        v_isShared_7931_ = v_isSharedCheck_7935_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7928_);
                        leanh::lean_dec(v___x_7904_);
                        v___x_7930_ = leanh::lean_box(0);
                        v_isShared_7931_ = v_isSharedCheck_7935_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_7909_ = leanh::lean_ctor_get(v___x_7902_, 0);
                leanh::lean_inc_ref(v_env_7909_);
                leanh::lean_dec(v___x_7902_);
                v_lctx_7910_ = leanh::lean_ctor_get(v___x_7903_, 0);
                v_isSharedCheck_7925_ = (!leanh::lean_is_exclusive(v___x_7903_)) as u8;
                if v_isSharedCheck_7925_ == 0 {
                    v_unused_7926_ = leanh::lean_ctor_get(v___x_7903_, 1);
                    leanh::lean_dec(v_unused_7926_);
                    v___x_7912_ = v___x_7903_;
                    v_isShared_7913_ = v_isSharedCheck_7925_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_7910_);
                    leanh::lean_dec(v___x_7903_);
                    v___x_7912_ = leanh::lean_box(0);
                    v_isShared_7913_ = v_isSharedCheck_7925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7914_ = (leanh::lean_unbox(v_a_7905_) as u8);
                leanh::lean_dec(v_a_7905_);
                v___x_7915_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_7910_, v___x_7914_);
                leanh::lean_dec_ref(v_lctx_7910_);
                v___x_7916_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_macroInline_spec__0_spec__0_spec__1_spec__3_spec__6_spec__16_spec__21___closed__2);
                leanh::lean_inc_ref(v_options_7900_);
                v___x_7917_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_7917_, 0, v_env_7909_);
                leanh::lean_ctor_set(v___x_7917_, 1, v___x_7916_);
                leanh::lean_ctor_set(v___x_7917_, 2, v___x_7915_);
                leanh::lean_ctor_set(v___x_7917_, 3, v_options_7900_);
                if v_isShared_7913_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7912_, 3);
                    leanh::lean_ctor_set(v___x_7912_, 1, v_msg_7894_);
                    leanh::lean_ctor_set(v___x_7912_, 0, v___x_7917_);
                    v___x_7919_ = v___x_7912_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7924_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7924_, 0, v___x_7917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7924_, 1, v_msg_7894_);
                    v___x_7919_ = v_reuseFailAlloc_7924_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ref_7901_);
                v___x_7920_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7920_, 0, v_ref_7901_);
                leanh::lean_ctor_set(v___x_7920_, 1, v___x_7919_);
                if v_isShared_7908_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7907_, 1);
                    leanh::lean_ctor_set(v___x_7907_, 0, v___x_7920_);
                    v___x_7922_ = v___x_7907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7923_, 0, v___x_7920_);
                    v___x_7922_ = v_reuseFailAlloc_7923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7922_;
            }
            5 => {
                if v_isShared_7931_ == 0 {
                    v___x_7933_ = v___x_7930_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7934_, 0, v_a_7928_);
                    v___x_7933_ = v_reuseFailAlloc_7934_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(
    mut v_msg_7936_: *mut leanh::LeanObject,
    mut v___y_7937_: *mut leanh::LeanObject,
    mut v___y_7938_: *mut leanh::LeanObject,
    mut v___y_7939_: *mut leanh::LeanObject,
    mut v___y_7940_: *mut leanh::LeanObject,
    mut v___y_7941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7942_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(
        v_msg_7936_,
        v___y_7937_,
        v___y_7938_,
        v___y_7939_,
        v___y_7940_,
    );
    leanh::lean_dec(v___y_7940_);
    leanh::lean_dec_ref(v___y_7939_);
    leanh::lean_dec(v___y_7938_);
    leanh::lean_dec_ref(v___y_7937_);
    return v_res_7942_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(
    mut v_00_u03b1_7943_: *mut leanh::LeanObject,
    mut v_msg_7944_: *mut leanh::LeanObject,
    mut v___y_7945_: *mut leanh::LeanObject,
    mut v___y_7946_: *mut leanh::LeanObject,
    mut v___y_7947_: *mut leanh::LeanObject,
    mut v___y_7948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7950_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(
        v_msg_7944_,
        v___y_7945_,
        v___y_7946_,
        v___y_7947_,
        v___y_7948_,
    );
    return v___x_7950_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(
    mut v_00_u03b1_7951_: *mut leanh::LeanObject,
    mut v_msg_7952_: *mut leanh::LeanObject,
    mut v___y_7953_: *mut leanh::LeanObject,
    mut v___y_7954_: *mut leanh::LeanObject,
    mut v___y_7955_: *mut leanh::LeanObject,
    mut v___y_7956_: *mut leanh::LeanObject,
    mut v___y_7957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7958_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(
        v_00_u03b1_7951_,
        v_msg_7952_,
        v___y_7953_,
        v___y_7954_,
        v___y_7955_,
        v___y_7956_,
    );
    leanh::lean_dec(v___y_7956_);
    leanh::lean_dec_ref(v___y_7955_);
    leanh::lean_dec(v___y_7954_);
    leanh::lean_dec_ref(v___y_7953_);
    return v_res_7958_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(
    mut v___x_7959_: u8,
    mut v_a_7960_: *mut leanh::LeanObject,
    mut v___y_7961_: *mut leanh::LeanObject,
    mut v___y_7962_: *mut leanh::LeanObject,
    mut v___y_7963_: *mut leanh::LeanObject,
    mut v___y_7964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7970_: u8 = 0;
    let mut v_binderName_7971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7975_: u8 = 0;
    let mut v___x_7976_: u8 = 0;
    let mut v___x_7977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7987_: u8 = 0;
    let mut v___x_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7991_: u8 = 0;
    let mut v___x_7992_: u8 = 0;
    let mut v___x_7993_: u8 = 0;
    let mut v_isSharedCheck_7994_: u8 = 0;
    let mut v_unused_7995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8004_: u8 = 0;
    let mut v_unused_8005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_7966_ = leanh::lean_ctor_get(v_a_7960_, 1);
                leanh::lean_inc(v_snd_7966_);
                if leanh::lean_obj_tag(v_snd_7966_) == 7 {
                    v_fst_7967_ = leanh::lean_ctor_get(v_a_7960_, 0);
                    v_isSharedCheck_7994_ = (!leanh::lean_is_exclusive(v_a_7960_)) as u8;
                    if v_isSharedCheck_7994_ == 0 {
                        v_unused_7995_ = leanh::lean_ctor_get(v_a_7960_, 1);
                        leanh::lean_dec(v_unused_7995_);
                        v___x_7969_ = v_a_7960_;
                        v_isShared_7970_ = v_isSharedCheck_7994_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_7967_);
                        leanh::lean_dec(v_a_7960_);
                        v___x_7969_ = leanh::lean_box(0);
                        v_isShared_7970_ = v_isSharedCheck_7994_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_7996_ = leanh::lean_ctor_get(v_a_7960_, 0);
                    v_isSharedCheck_8004_ = (!leanh::lean_is_exclusive(v_a_7960_)) as u8;
                    if v_isSharedCheck_8004_ == 0 {
                        v_unused_8005_ = leanh::lean_ctor_get(v_a_7960_, 1);
                        leanh::lean_dec(v_unused_8005_);
                        v___x_7998_ = v_a_7960_;
                        v_isShared_7999_ = v_isSharedCheck_8004_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_7996_);
                        leanh::lean_dec(v_a_7960_);
                        v___x_7998_ = leanh::lean_box(0);
                        v_isShared_7999_ = v_isSharedCheck_8004_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_binderName_7971_ = leanh::lean_ctor_get(v_snd_7966_, 0);
                leanh::lean_inc(v_binderName_7971_);
                v_binderType_7972_ = leanh::lean_ctor_get(v_snd_7966_, 1);
                leanh::lean_inc_ref(v_binderType_7972_);
                v_body_7973_ = leanh::lean_ctor_get(v_snd_7966_, 2);
                leanh::lean_inc_ref(v_body_7973_);
                leanh::lean_dec_ref_known(v_snd_7966_, 3);
                if v___x_7959_ == 0 {
                    v___x_7992_ = l_Lean_isMarkedBorrowed(v_binderType_7972_);
                    v___y_7975_ = v___x_7992_;
                    state = 2;
                    continue;
                } else {
                    v___x_7993_ = 0;
                    v___y_7975_ = v___x_7993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7976_ = 0;
                v___x_7977_ = l_Lean_Compiler_LCNF_mkParam(
                    v___x_7976_,
                    v_binderName_7971_,
                    v_binderType_7972_,
                    v___y_7975_,
                    v___y_7961_,
                    v___y_7962_,
                    v___y_7963_,
                    v___y_7964_,
                );
                if leanh::lean_obj_tag(v___x_7977_) == 0 {
                    v_a_7978_ = leanh::lean_ctor_get(v___x_7977_, 0);
                    leanh::lean_inc(v_a_7978_);
                    leanh::lean_dec_ref_known(v___x_7977_, 1);
                    v___x_7979_ = lean_array_push(v_fst_7967_, v_a_7978_);
                    if v_isShared_7970_ == 0 {
                        leanh::lean_ctor_set(v___x_7969_, 1, v_body_7973_);
                        leanh::lean_ctor_set(v___x_7969_, 0, v___x_7979_);
                        v___x_7981_ = v___x_7969_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7983_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7983_, 0, v___x_7979_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7983_, 1, v_body_7973_);
                        v___x_7981_ = v_reuseFailAlloc_7983_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_body_7973_);
                    leanh::lean_del_object(v___x_7969_);
                    leanh::lean_dec(v_fst_7967_);
                    v_a_7984_ = leanh::lean_ctor_get(v___x_7977_, 0);
                    v_isSharedCheck_7991_ = (!leanh::lean_is_exclusive(v___x_7977_)) as u8;
                    if v_isSharedCheck_7991_ == 0 {
                        v___x_7986_ = v___x_7977_;
                        v_isShared_7987_ = v_isSharedCheck_7991_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7984_);
                        leanh::lean_dec(v___x_7977_);
                        v___x_7986_ = leanh::lean_box(0);
                        v_isShared_7987_ = v_isSharedCheck_7991_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_7960_ = v___x_7981_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_7987_ == 0 {
                    v___x_7989_ = v___x_7986_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7990_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7990_, 0, v_a_7984_);
                    v___x_7989_ = v_reuseFailAlloc_7990_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7989_;
            }
            6 => {
                if v_isShared_7999_ == 0 {
                    v___x_8001_ = v___x_7998_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8003_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8003_, 0, v_fst_7996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8003_, 1, v_snd_7966_);
                    v___x_8001_ = v_reuseFailAlloc_8003_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_8002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8002_, 0, v___x_8001_);
                return v___x_8002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(
    mut v___x_8006_: *mut leanh::LeanObject,
    mut v_a_8007_: *mut leanh::LeanObject,
    mut v___y_8008_: *mut leanh::LeanObject,
    mut v___y_8009_: *mut leanh::LeanObject,
    mut v___y_8010_: *mut leanh::LeanObject,
    mut v___y_8011_: *mut leanh::LeanObject,
    mut v___y_8012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_15283__boxed_8013_: u8 = 0;
    let mut v_res_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_15283__boxed_8013_ = (leanh::lean_unbox(v___x_8006_) as u8);
    v_res_8014_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(
            v___x_15283__boxed_8013_,
            v_a_8007_,
            v___y_8008_,
            v___y_8009_,
            v___y_8010_,
            v___y_8011_,
        );
    leanh::lean_dec(v___y_8011_);
    leanh::lean_dec_ref(v___y_8010_);
    leanh::lean_dec(v___y_8009_);
    leanh::lean_dec_ref(v___y_8008_);
    return v_res_8014_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toDecl___lam__0(
    mut v_expr_8017_: *mut leanh::LeanObject,
    mut v___y_8018_: *mut leanh::LeanObject,
    mut v___y_8019_: *mut leanh::LeanObject,
    mut v___y_8020_: *mut leanh::LeanObject,
    mut v___y_8021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_8023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: u8 = 0;
    let mut v___x_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8032_: u8 = 0;
    let mut v_fst_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8037_: u8 = 0;
    let mut v_a_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8041_: u8 = 0;
    let mut v___x_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_8023_ = leanh::lean_ctor_get(v___y_8020_, 2);
                v___x_8024_ = l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0;
                v___x_8025_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
                v___x_8026_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(
                    v_options_8023_,
                    v___x_8025_,
                );
                v___x_8027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8027_, 0, v___x_8024_);
                leanh::lean_ctor_set(v___x_8027_, 1, v_expr_8017_);
                v___x_8028_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_8026_, v___x_8027_, v___y_8018_, v___y_8019_, v___y_8020_, v___y_8021_);
                if leanh::lean_obj_tag(v___x_8028_) == 0 {
                    v_a_8029_ = leanh::lean_ctor_get(v___x_8028_, 0);
                    v_isSharedCheck_8037_ = (!leanh::lean_is_exclusive(v___x_8028_)) as u8;
                    if v_isSharedCheck_8037_ == 0 {
                        v___x_8031_ = v___x_8028_;
                        v_isShared_8032_ = v_isSharedCheck_8037_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8029_);
                        leanh::lean_dec(v___x_8028_);
                        v___x_8031_ = leanh::lean_box(0);
                        v_isShared_8032_ = v_isSharedCheck_8037_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8038_ = leanh::lean_ctor_get(v___x_8028_, 0);
                    v_isSharedCheck_8045_ = (!leanh::lean_is_exclusive(v___x_8028_)) as u8;
                    if v_isSharedCheck_8045_ == 0 {
                        v___x_8040_ = v___x_8028_;
                        v_isShared_8041_ = v_isSharedCheck_8045_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8038_);
                        leanh::lean_dec(v___x_8028_);
                        v___x_8040_ = leanh::lean_box(0);
                        v_isShared_8041_ = v_isSharedCheck_8045_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_8033_ = leanh::lean_ctor_get(v_a_8029_, 0);
                leanh::lean_inc(v_fst_8033_);
                leanh::lean_dec(v_a_8029_);
                if v_isShared_8032_ == 0 {
                    leanh::lean_ctor_set(v___x_8031_, 0, v_fst_8033_);
                    v___x_8035_ = v___x_8031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8036_, 0, v_fst_8033_);
                    v___x_8035_ = v_reuseFailAlloc_8036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8035_;
            }
            3 => {
                if v_isShared_8041_ == 0 {
                    v___x_8043_ = v___x_8040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8044_, 0, v_a_8038_);
                    v___x_8043_ = v_reuseFailAlloc_8044_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(
    mut v_expr_8046_: *mut leanh::LeanObject,
    mut v___y_8047_: *mut leanh::LeanObject,
    mut v___y_8048_: *mut leanh::LeanObject,
    mut v___y_8049_: *mut leanh::LeanObject,
    mut v___y_8050_: *mut leanh::LeanObject,
    mut v___y_8051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8052_ = l_Lean_Compiler_LCNF_toDecl___lam__0(
        v_expr_8046_,
        v___y_8047_,
        v___y_8048_,
        v___y_8049_,
        v___y_8050_,
    );
    leanh::lean_dec(v___y_8050_);
    leanh::lean_dec_ref(v___y_8049_);
    leanh::lean_dec(v___y_8048_);
    leanh::lean_dec_ref(v___y_8047_);
    return v_res_8052_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toDecl___lam__1(
    mut v___x_8053_: u8,
    mut v___x_8054_: u8,
    mut v_xs_8055_: *mut leanh::LeanObject,
    mut v_body_8056_: *mut leanh::LeanObject,
    mut v___y_8057_: *mut leanh::LeanObject,
    mut v___y_8058_: *mut leanh::LeanObject,
    mut v___y_8059_: *mut leanh::LeanObject,
    mut v___y_8060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8062_ = l_Lean_Meta_etaExpand(
        v_body_8056_,
        v___y_8057_,
        v___y_8058_,
        v___y_8059_,
        v___y_8060_,
    );
    if leanh::lean_obj_tag(v___x_8062_) == 0 {
        let mut v_a_8063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8064_: u8 = 0;
        let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_8063_ = leanh::lean_ctor_get(v___x_8062_, 0);
        leanh::lean_inc(v_a_8063_);
        leanh::lean_dec_ref_known(v___x_8062_, 1);
        v___x_8064_ = 1;
        v___x_8065_ = l_Lean_Meta_mkLambdaFVars(
            v_xs_8055_,
            v_a_8063_,
            v___x_8053_,
            v___x_8054_,
            v___x_8053_,
            v___x_8054_,
            v___x_8064_,
            v___y_8057_,
            v___y_8058_,
            v___y_8059_,
            v___y_8060_,
        );
        return v___x_8065_;
    } else {
        return v___x_8062_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(
    mut v___x_8066_: *mut leanh::LeanObject,
    mut v___x_8067_: *mut leanh::LeanObject,
    mut v_xs_8068_: *mut leanh::LeanObject,
    mut v_body_8069_: *mut leanh::LeanObject,
    mut v___y_8070_: *mut leanh::LeanObject,
    mut v___y_8071_: *mut leanh::LeanObject,
    mut v___y_8072_: *mut leanh::LeanObject,
    mut v___y_8073_: *mut leanh::LeanObject,
    mut v___y_8074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_15439__boxed_8075_: u8 = 0;
    let mut v___x_15440__boxed_8076_: u8 = 0;
    let mut v_res_8077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_15439__boxed_8075_ = (leanh::lean_unbox(v___x_8066_) as u8);
    v___x_15440__boxed_8076_ = (leanh::lean_unbox(v___x_8067_) as u8);
    v_res_8077_ = l_Lean_Compiler_LCNF_toDecl___lam__1(
        v___x_15439__boxed_8075_,
        v___x_15440__boxed_8076_,
        v_xs_8068_,
        v_body_8069_,
        v___y_8070_,
        v___y_8071_,
        v___y_8072_,
        v___y_8073_,
    );
    leanh::lean_dec(v___y_8073_);
    leanh::lean_dec_ref(v___y_8072_);
    leanh::lean_dec(v___y_8071_);
    leanh::lean_dec_ref(v___y_8070_);
    leanh::lean_dec_ref(v_xs_8068_);
    return v_res_8077_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(
    mut v_as_8078_: *mut leanh::LeanObject,
    mut v_i_8079_: usize,
    mut v_stop_8080_: usize,
) -> u8 {
    let mut v___x_8081_: u8 = 0;
    let mut v___x_8082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_8083_: u8 = 0;
    let mut v___x_8084_: usize = 0;
    let mut v___x_8085_: usize = 0;
    let mut v___x_8087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8081_ = lean_usize_dec_eq(v_i_8079_, v_stop_8080_);
                if v___x_8081_ == 0 {
                    v___x_8082_ = lean_array_uget_borrowed(v_as_8078_, v_i_8079_);
                    v_borrow_8083_ = leanh::lean_ctor_get_uint8(
                        v___x_8082_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_borrow_8083_ == 0 {
                        v___x_8084_ = 1usize;
                        v___x_8085_ = lean_usize_add(v_i_8079_, v___x_8084_);
                        v_i_8079_ = v___x_8085_;
                        state = 0;
                        continue;
                    } else {
                        return v_borrow_8083_;
                    }
                } else {
                    v___x_8087_ = 0;
                    return v___x_8087_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(
    mut v_as_8088_: *mut leanh::LeanObject,
    mut v_i_8089_: *mut leanh::LeanObject,
    mut v_stop_8090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_8091_: usize = 0;
    let mut v_stop_boxed_8092_: usize = 0;
    let mut v_res_8093_: u8 = 0;
    let mut v_r_8094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_8091_ = leanh::lean_unbox_usize(v_i_8089_);
    leanh::lean_dec(v_i_8089_);
    v_stop_boxed_8092_ = leanh::lean_unbox_usize(v_stop_8090_);
    leanh::lean_dec(v_stop_8090_);
    v_res_8093_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_8088_, v_i_boxed_8091_, v_stop_boxed_8092_);
    leanh::lean_dec_ref(v_as_8088_);
    v_r_8094_ = leanh::lean_box((v_res_8093_) as usize);
    return v_r_8094_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(
    mut v___x_8095_: u8,
    mut v_sz_8096_: usize,
    mut v_i_8097_: usize,
    mut v_bs_8098_: *mut leanh::LeanObject,
    mut v___y_8099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8101_: u8 = 0;
    let mut v___x_8102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_8103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8104_: u8 = 0;
    let mut v___x_8105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: usize = 0;
    let mut v___x_8110_: usize = 0;
    let mut v___x_8111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8116_: u8 = 0;
    let mut v___x_8118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8101_ = lean_usize_dec_lt(v_i_8097_, v_sz_8096_);
                if v___x_8101_ == 0 {
                    v___x_8102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8102_, 0, v_bs_8098_);
                    return v___x_8102_;
                } else {
                    v_v_8103_ = lean_array_uget_borrowed(v_bs_8098_, v_i_8097_);
                    v___x_8104_ = 0;
                    leanh::lean_inc(v_v_8103_);
                    v___x_8105_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_8104_, v_v_8103_, v___x_8095_, v___y_8099_);
                    if leanh::lean_obj_tag(v___x_8105_) == 0 {
                        v_a_8106_ = leanh::lean_ctor_get(v___x_8105_, 0);
                        leanh::lean_inc(v_a_8106_);
                        leanh::lean_dec_ref_known(v___x_8105_, 1);
                        v___x_8107_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_8108_ = lean_array_uset(v_bs_8098_, v_i_8097_, v___x_8107_);
                        v___x_8109_ = 1usize;
                        v___x_8110_ = lean_usize_add(v_i_8097_, v___x_8109_);
                        v___x_8111_ = lean_array_uset(v_bs_x27_8108_, v_i_8097_, v_a_8106_);
                        v_i_8097_ = v___x_8110_;
                        v_bs_8098_ = v___x_8111_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_8098_);
                        v_a_8113_ = leanh::lean_ctor_get(v___x_8105_, 0);
                        v_isSharedCheck_8120_ =
                            (!leanh::lean_is_exclusive(v___x_8105_)) as u8;
                        if v_isSharedCheck_8120_ == 0 {
                            v___x_8115_ = v___x_8105_;
                            v_isShared_8116_ = v_isSharedCheck_8120_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8113_);
                            leanh::lean_dec(v___x_8105_);
                            v___x_8115_ = leanh::lean_box(0);
                            v_isShared_8116_ = v_isSharedCheck_8120_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8116_ == 0 {
                    v___x_8118_ = v___x_8115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8119_, 0, v_a_8113_);
                    v___x_8118_ = v_reuseFailAlloc_8119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(
    mut v___x_8121_: *mut leanh::LeanObject,
    mut v_sz_8122_: *mut leanh::LeanObject,
    mut v_i_8123_: *mut leanh::LeanObject,
    mut v_bs_8124_: *mut leanh::LeanObject,
    mut v___y_8125_: *mut leanh::LeanObject,
    mut v___y_8126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_15481__boxed_8127_: u8 = 0;
    let mut v_sz_boxed_8128_: usize = 0;
    let mut v_i_boxed_8129_: usize = 0;
    let mut v_res_8130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_15481__boxed_8127_ = (leanh::lean_unbox(v___x_8121_) as u8);
    v_sz_boxed_8128_ = leanh::lean_unbox_usize(v_sz_8122_);
    leanh::lean_dec(v_sz_8122_);
    v_i_boxed_8129_ = leanh::lean_unbox_usize(v_i_8123_);
    leanh::lean_dec(v_i_8123_);
    v_res_8130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_15481__boxed_8127_, v_sz_boxed_8128_, v_i_boxed_8129_, v_bs_8124_, v___y_8125_);
    leanh::lean_dec(v___y_8125_);
    return v_res_8130_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toDecl___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_8132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8132_ = l_Lean_Compiler_LCNF_toDecl___closed__0;
    v___x_8133_ = l_Lean_stringToMessageData(v___x_8132_);
    return v___x_8133_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toDecl___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_8135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8135_ = l_Lean_Compiler_LCNF_toDecl___closed__2;
    v___x_8136_ = l_Lean_stringToMessageData(v___x_8135_);
    return v___x_8136_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_8140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8140_ = l_Lean_Compiler_LCNF_toDecl___closed__5;
    v___x_8141_ = l_Lean_stringToMessageData(v___x_8140_);
    return v___x_8141_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toDecl___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_8143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8143_ = l_Lean_Compiler_LCNF_toDecl___closed__7;
    v___x_8144_ = l_Lean_stringToMessageData(v___x_8143_);
    return v___x_8144_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toDecl___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_8146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8146_ = l_Lean_Compiler_LCNF_toDecl___closed__9;
    v___x_8147_ = l_Lean_stringToMessageData(v___x_8146_);
    return v___x_8147_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toDecl(
    mut v_declName_8148_: *mut leanh::LeanObject,
    mut v_a_8149_: *mut leanh::LeanObject,
    mut v_a_8150_: *mut leanh::LeanObject,
    mut v_a_8151_: *mut leanh::LeanObject,
    mut v_a_8152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8161_: u8 = 0;
    let mut v___x_8162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8172_: u8 = 0;
    let mut v___x_8174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8176_: u8 = 0;
    let mut v___y_8178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8180_: u8 = 0;
    let mut v_decl_8181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_8182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_8183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8188_: u8 = 0;
    let mut v___x_8189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8190_: u8 = 0;
    let mut v___x_8191_: usize = 0;
    let mut v___x_8192_: usize = 0;
    let mut v___x_8193_: u8 = 0;
    let mut v___y_8195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8197_: u8 = 0;
    let mut v_decl_8198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8207_: u8 = 0;
    let mut v_toSignature_8208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_8209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_8210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_8211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_8213_: u8 = 0;
    let mut v_inlineAttr_x3f_8214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8217_: u8 = 0;
    let mut v_name_8218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_8221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_8222_: u8 = 0;
    let mut v___x_8224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8225_: u8 = 0;
    let mut v_sz_8226_: usize = 0;
    let mut v___x_8227_: usize = 0;
    let mut v___x_8228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8239_: u8 = 0;
    let mut v___x_8241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8243_: u8 = 0;
    let mut v_isSharedCheck_8244_: u8 = 0;
    let mut v_isSharedCheck_8245_: u8 = 0;
    let mut v___y_8247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8250_: u8 = 0;
    let mut v___y_8251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8255_: u8 = 0;
    let mut v___y_8256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8266_: u8 = 0;
    let mut v___y_8267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8271_: u8 = 0;
    let mut v_a_8272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8277_: u8 = 0;
    let mut v___x_8278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8285_: u8 = 0;
    let mut v_a_8286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8289_: u8 = 0;
    let mut v___x_8291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8293_: u8 = 0;
    let mut v___y_8295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8296_: u8 = 0;
    let mut v___y_8297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8299_: u8 = 0;
    let mut v_a_8300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8305_: u8 = 0;
    let mut v___x_8306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8313_: u8 = 0;
    let mut v_a_8314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8317_: u8 = 0;
    let mut v___x_8319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8321_: u8 = 0;
    let mut v___x_8322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8335_: u8 = 0;
    let mut v___x_8336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: u8 = 0;
    let mut v_a_8344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: u8 = 0;
    let mut v_a_8346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8349_: u8 = 0;
    let mut v___x_8351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8353_: u8 = 0;
    let mut v___x_8354_: u8 = 0;
    let mut v___x_8355_: u8 = 0;
    let mut v___x_8356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: u8 = 0;
    let mut v___x_8359_: u8 = 0;
    let mut v___x_8360_: u8 = 0;
    let mut v___x_8361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8362_: u64 = 0;
    let mut v___x_8363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_8391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8394_: u8 = 0;
    let mut v___x_8395_: u8 = 0;
    let mut v___x_8396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_8397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8401_: u8 = 0;
    let mut v___x_8403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8409_: u8 = 0;
    let mut v___x_8411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8413_: u8 = 0;
    let mut v_isSharedCheck_8414_: u8 = 0;
    let mut v_unused_8415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8416_: u8 = 0;
    let mut v___x_8417_: u8 = 0;
    let mut v_a_8418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8421_: u8 = 0;
    let mut v___x_8423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8425_: u8 = 0;
    let mut v_a_8426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8429_: u8 = 0;
    let mut v___x_8431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8433_: u8 = 0;
    let mut v_a_8434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8437_: u8 = 0;
    let mut v___x_8439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8441_: u8 = 0;
    let mut v_a_8442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8445_: u8 = 0;
    let mut v___x_8447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8449_: u8 = 0;
    let mut v_a_8450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8453_: u8 = 0;
    let mut v___x_8455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8457_: u8 = 0;
    let mut v_a_8458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8461_: u8 = 0;
    let mut v___x_8463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8465_: u8 = 0;
    let mut v_a_8466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8469_: u8 = 0;
    let mut v___x_8471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8473_: u8 = 0;
    let mut v___x_8474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8480_: u8 = 0;
    let mut v___x_8481_: u8 = 0;
    let mut v___x_8482_: u8 = 0;
    let mut v___x_8483_: u8 = 0;
    let mut v___x_8484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: u64 = 0;
    let mut v___x_8486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8498_: u8 = 0;
    let mut v_a_8499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: u8 = 0;
    let mut v_a_8501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8504_: u8 = 0;
    let mut v___x_8506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8508_: u8 = 0;
    let mut v___x_8509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8510_: u8 = 0;
    let mut v___x_8511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8322_ = leanh::lean_box(1);
                v___x_8516_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_8148_);
                if leanh::lean_obj_tag(v___x_8516_) == 1 {
                    leanh::lean_dec(v_declName_8148_);
                    v_val_8517_ = leanh::lean_ctor_get(v___x_8516_, 0);
                    leanh::lean_inc(v_val_8517_);
                    leanh::lean_dec_ref_known(v___x_8516_, 1);
                    v___y_8324_ = v_val_8517_;
                    state = 23;
                    continue;
                } else {
                    leanh::lean_dec(v___x_8516_);
                    v___y_8324_ = v_declName_8148_;
                    state = 23;
                    continue;
                }
            }
            1 => {
                if v___y_8161_ == 0 {
                    leanh::lean_dec(v___y_8157_);
                    v___x_8162_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8162_, 0, v___y_8155_);
                    return v___x_8162_;
                } else {
                    leanh::lean_dec_ref(v___y_8155_);
                    v___x_8163_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_toDecl___closed__1,
                    );
                    v___x_8164_ = l_Lean_MessageData_ofName(v___y_8157_);
                    v___x_8165_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8165_, 0, v___x_8163_);
                    leanh::lean_ctor_set(v___x_8165_, 1, v___x_8164_);
                    v___x_8166_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__3_once),
                        _init_l_Lean_Compiler_LCNF_toDecl___closed__3,
                    );
                    v___x_8167_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8167_, 0, v___x_8165_);
                    leanh::lean_ctor_set(v___x_8167_, 1, v___x_8166_);
                    v___x_8168_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(
                            v___x_8167_,
                            v___y_8156_,
                            v___y_8159_,
                            v___y_8160_,
                            v___y_8158_,
                        );
                    v_a_8169_ = leanh::lean_ctor_get(v___x_8168_, 0);
                    v_isSharedCheck_8176_ = (!leanh::lean_is_exclusive(v___x_8168_)) as u8;
                    if v_isSharedCheck_8176_ == 0 {
                        v___x_8171_ = v___x_8168_;
                        v_isShared_8172_ = v_isSharedCheck_8176_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8169_);
                        leanh::lean_dec(v___x_8168_);
                        v___x_8171_ = leanh::lean_box(0);
                        v_isShared_8172_ = v_isSharedCheck_8176_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8172_ == 0 {
                    v___x_8174_ = v___x_8171_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8175_, 0, v_a_8169_);
                    v___x_8174_ = v_reuseFailAlloc_8175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8174_;
            }
            4 => {
                leanh::lean_inc(v_name_8182_);
                v___x_8188_ = l_Lean_isExport(v___y_8179_, v_name_8182_);
                if v___x_8188_ == 0 {
                    leanh::lean_dec_ref(v_params_8183_);
                    v___y_8155_ = v_decl_8181_;
                    v___y_8156_ = v___y_8184_;
                    v___y_8157_ = v_name_8182_;
                    v___y_8158_ = v___y_8187_;
                    v___y_8159_ = v___y_8185_;
                    v___y_8160_ = v___y_8186_;
                    v___y_8161_ = v___y_8180_;
                    state = 1;
                    continue;
                } else {
                    v___x_8189_ = lean_array_get_size(v_params_8183_);
                    v___x_8190_ = lean_nat_dec_lt(v___y_8178_, v___x_8189_);
                    if v___x_8190_ == 0 {
                        leanh::lean_dec_ref(v_params_8183_);
                        v___y_8155_ = v_decl_8181_;
                        v___y_8156_ = v___y_8184_;
                        v___y_8157_ = v_name_8182_;
                        v___y_8158_ = v___y_8187_;
                        v___y_8159_ = v___y_8185_;
                        v___y_8160_ = v___y_8186_;
                        v___y_8161_ = v___y_8180_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_8190_ == 0 {
                            leanh::lean_dec_ref(v_params_8183_);
                            v___y_8155_ = v_decl_8181_;
                            v___y_8156_ = v___y_8184_;
                            v___y_8157_ = v_name_8182_;
                            v___y_8158_ = v___y_8187_;
                            v___y_8159_ = v___y_8185_;
                            v___y_8160_ = v___y_8186_;
                            v___y_8161_ = v___y_8180_;
                            state = 1;
                            continue;
                        } else {
                            v___x_8191_ = 0usize;
                            v___x_8192_ = lean_usize_of_nat(v___x_8189_);
                            v___x_8193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_8183_, v___x_8191_, v___x_8192_);
                            leanh::lean_dec_ref(v_params_8183_);
                            v___y_8155_ = v_decl_8181_;
                            v___y_8156_ = v___y_8184_;
                            v___y_8157_ = v_name_8182_;
                            v___y_8158_ = v___y_8187_;
                            v___y_8159_ = v___y_8185_;
                            v___y_8160_ = v___y_8186_;
                            v___y_8161_ = v___x_8193_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_8203_ = l_Lean_Compiler_LCNF_Decl_etaExpand(
                    v_decl_8198_,
                    v___y_8199_,
                    v___y_8200_,
                    v___y_8201_,
                    v___y_8202_,
                );
                if leanh::lean_obj_tag(v___x_8203_) == 0 {
                    v_a_8204_ = leanh::lean_ctor_get(v___x_8203_, 0);
                    leanh::lean_inc(v_a_8204_);
                    leanh::lean_dec_ref_known(v___x_8203_, 1);
                    v_options_8205_ = leanh::lean_ctor_get(v___y_8201_, 2);
                    v___x_8206_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
                    v___x_8207_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(
                        v_options_8205_,
                        v___x_8206_,
                    );
                    if v___x_8207_ == 0 {
                        v_toSignature_8208_ = leanh::lean_ctor_get(v_a_8204_, 0);
                        v_name_8209_ = leanh::lean_ctor_get(v_toSignature_8208_, 0);
                        leanh::lean_inc(v_name_8209_);
                        v_params_8210_ = leanh::lean_ctor_get(v_toSignature_8208_, 3);
                        leanh::lean_inc_ref(v_params_8210_);
                        v___y_8178_ = v___y_8195_;
                        v___y_8179_ = v___y_8196_;
                        v___y_8180_ = v___y_8197_;
                        v_decl_8181_ = v_a_8204_;
                        v_name_8182_ = v_name_8209_;
                        v_params_8183_ = v_params_8210_;
                        v___y_8184_ = v___y_8199_;
                        v___y_8185_ = v___y_8200_;
                        v___y_8186_ = v___y_8201_;
                        v___y_8187_ = v___y_8202_;
                        state = 4;
                        continue;
                    } else {
                        v_toSignature_8211_ = leanh::lean_ctor_get(v_a_8204_, 0);
                        v_value_8212_ = leanh::lean_ctor_get(v_a_8204_, 1);
                        v_recursive_8213_ = leanh::lean_ctor_get_uint8(
                            v_a_8204_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_inlineAttr_x3f_8214_ = leanh::lean_ctor_get(v_a_8204_, 2);
                        v_isSharedCheck_8245_ = (!leanh::lean_is_exclusive(v_a_8204_)) as u8;
                        if v_isSharedCheck_8245_ == 0 {
                            v___x_8216_ = v_a_8204_;
                            v_isShared_8217_ = v_isSharedCheck_8245_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_inlineAttr_x3f_8214_);
                            leanh::lean_inc(v_value_8212_);
                            leanh::lean_inc(v_toSignature_8211_);
                            leanh::lean_dec(v_a_8204_);
                            v___x_8216_ = leanh::lean_box(0);
                            v_isShared_8217_ = v_isSharedCheck_8245_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_8196_);
                    return v___x_8203_;
                }
            }
            6 => {
                v_name_8218_ = leanh::lean_ctor_get(v_toSignature_8211_, 0);
                v_levelParams_8219_ = leanh::lean_ctor_get(v_toSignature_8211_, 1);
                v_type_8220_ = leanh::lean_ctor_get(v_toSignature_8211_, 2);
                v_params_8221_ = leanh::lean_ctor_get(v_toSignature_8211_, 3);
                v_safe_8222_ = leanh::lean_ctor_get_uint8(
                    v_toSignature_8211_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_8244_ =
                    (!leanh::lean_is_exclusive(v_toSignature_8211_)) as u8;
                if v_isSharedCheck_8244_ == 0 {
                    v___x_8224_ = v_toSignature_8211_;
                    v_isShared_8225_ = v_isSharedCheck_8244_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_params_8221_);
                    leanh::lean_inc(v_type_8220_);
                    leanh::lean_inc(v_levelParams_8219_);
                    leanh::lean_inc(v_name_8218_);
                    leanh::lean_dec(v_toSignature_8211_);
                    v___x_8224_ = leanh::lean_box(0);
                    v_isShared_8225_ = v_isSharedCheck_8244_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_sz_8226_ = lean_array_size(v_params_8221_);
                v___x_8227_ = 0usize;
                v___x_8228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___y_8197_, v_sz_8226_, v___x_8227_, v_params_8221_, v___y_8200_);
                if leanh::lean_obj_tag(v___x_8228_) == 0 {
                    v_a_8229_ = leanh::lean_ctor_get(v___x_8228_, 0);
                    leanh::lean_inc_n(v_a_8229_, 2);
                    leanh::lean_dec_ref_known(v___x_8228_, 1);
                    leanh::lean_inc(v_name_8218_);
                    if v_isShared_8225_ == 0 {
                        leanh::lean_ctor_set(v___x_8224_, 3, v_a_8229_);
                        v___x_8231_ = v___x_8224_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_8235_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8235_, 0, v_name_8218_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8235_, 1, v_levelParams_8219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8235_, 2, v_type_8220_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8235_, 3, v_a_8229_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_8235_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                            v_safe_8222_,
                        );
                        v___x_8231_ = v_reuseFailAlloc_8235_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8224_);
                    leanh::lean_dec_ref(v_type_8220_);
                    leanh::lean_dec(v_levelParams_8219_);
                    leanh::lean_dec(v_name_8218_);
                    leanh::lean_del_object(v___x_8216_);
                    leanh::lean_dec(v_inlineAttr_x3f_8214_);
                    leanh::lean_dec_ref(v_value_8212_);
                    leanh::lean_dec_ref(v___y_8196_);
                    v_a_8236_ = leanh::lean_ctor_get(v___x_8228_, 0);
                    v_isSharedCheck_8243_ = (!leanh::lean_is_exclusive(v___x_8228_)) as u8;
                    if v_isSharedCheck_8243_ == 0 {
                        v___x_8238_ = v___x_8228_;
                        v_isShared_8239_ = v_isSharedCheck_8243_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8236_);
                        leanh::lean_dec(v___x_8228_);
                        v___x_8238_ = leanh::lean_box(0);
                        v_isShared_8239_ = v_isSharedCheck_8243_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_8217_ == 0 {
                    leanh::lean_ctor_set(v___x_8216_, 0, v___x_8231_);
                    v___x_8233_ = v___x_8216_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8234_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8234_, 0, v___x_8231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8234_, 1, v_value_8212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8234_, 2, v_inlineAttr_x3f_8214_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8234_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_recursive_8213_,
                    );
                    v___x_8233_ = v_reuseFailAlloc_8234_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_8178_ = v___y_8195_;
                v___y_8179_ = v___y_8196_;
                v___y_8180_ = v___y_8197_;
                v_decl_8181_ = v___x_8233_;
                v_name_8182_ = v_name_8218_;
                v_params_8183_ = v_a_8229_;
                v___y_8184_ = v___y_8199_;
                v___y_8185_ = v___y_8200_;
                v___y_8186_ = v___y_8201_;
                v___y_8187_ = v___y_8202_;
                state = 4;
                continue;
            }
            10 => {
                if v_isShared_8239_ == 0 {
                    v___x_8241_ = v___x_8238_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8242_, 0, v_a_8236_);
                    v___x_8241_ = v_reuseFailAlloc_8242_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8241_;
            }
            12 => {
                v___x_8260_ = l_Lean_ConstantInfo_levelParams(v___y_8247_);
                leanh::lean_dec_ref(v___y_8247_);
                v___x_8261_ = lean_mk_empty_array_with_capacity(v___y_8248_);
                v___x_8262_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_8262_, 0, v___y_8252_);
                leanh::lean_ctor_set(v___x_8262_, 1, v___x_8260_);
                leanh::lean_ctor_set(v___x_8262_, 2, v___y_8251_);
                leanh::lean_ctor_set(v___x_8262_, 3, v___x_8261_);
                leanh::lean_ctor_set_uint8(
                    v___x_8262_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_8255_,
                );
                v___x_8263_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8263_, 0, v___y_8253_);
                v___x_8264_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_8264_, 0, v___x_8262_);
                leanh::lean_ctor_set(v___x_8264_, 1, v___x_8263_);
                leanh::lean_ctor_set(v___x_8264_, 2, v___y_8254_);
                leanh::lean_ctor_set_uint8(
                    v___x_8264_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_8250_,
                );
                v___y_8195_ = v___y_8248_;
                v___y_8196_ = v___y_8249_;
                v___y_8197_ = v___y_8250_;
                v_decl_8198_ = v___x_8264_;
                v___y_8199_ = v___y_8256_;
                v___y_8200_ = v___y_8257_;
                v___y_8201_ = v___y_8258_;
                v___y_8202_ = v___y_8259_;
                state = 5;
                continue;
            }
            13 => {
                leanh::lean_inc_ref(v_a_8272_);
                v___x_8273_ = l_Lean_Compiler_LCNF_toDecl___lam__0(
                    v_a_8272_, v_a_8149_, v_a_8150_, v_a_8151_, v_a_8152_,
                );
                if leanh::lean_obj_tag(v___x_8273_) == 0 {
                    v_a_8274_ = leanh::lean_ctor_get(v___x_8273_, 0);
                    v_isSharedCheck_8285_ = (!leanh::lean_is_exclusive(v___x_8273_)) as u8;
                    if v_isSharedCheck_8285_ == 0 {
                        v___x_8276_ = v___x_8273_;
                        v_isShared_8277_ = v_isSharedCheck_8285_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8274_);
                        leanh::lean_dec(v___x_8273_);
                        v___x_8276_ = leanh::lean_box(0);
                        v_isShared_8277_ = v_isSharedCheck_8285_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_8272_);
                    leanh::lean_dec(v___y_8270_);
                    leanh::lean_dec(v___y_8269_);
                    leanh::lean_dec(v___y_8268_);
                    leanh::lean_dec_ref(v___y_8267_);
                    v_a_8286_ = leanh::lean_ctor_get(v___x_8273_, 0);
                    v_isSharedCheck_8293_ = (!leanh::lean_is_exclusive(v___x_8273_)) as u8;
                    if v_isSharedCheck_8293_ == 0 {
                        v___x_8288_ = v___x_8273_;
                        v_isShared_8289_ = v_isSharedCheck_8293_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8286_);
                        leanh::lean_dec(v___x_8273_);
                        v___x_8288_ = leanh::lean_box(0);
                        v_isShared_8289_ = v_isSharedCheck_8293_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                v___x_8278_ = l_Lean_ConstantInfo_levelParams(v___y_8267_);
                leanh::lean_dec_ref(v___y_8267_);
                v___x_8279_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_8279_, 0, v___y_8269_);
                leanh::lean_ctor_set(v___x_8279_, 1, v___x_8278_);
                leanh::lean_ctor_set(v___x_8279_, 2, v_a_8272_);
                leanh::lean_ctor_set(v___x_8279_, 3, v_a_8274_);
                leanh::lean_ctor_set_uint8(
                    v___x_8279_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_8271_,
                );
                v___x_8280_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8280_, 0, v___y_8268_);
                v___x_8281_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_8281_, 0, v___x_8279_);
                leanh::lean_ctor_set(v___x_8281_, 1, v___x_8280_);
                leanh::lean_ctor_set(v___x_8281_, 2, v___y_8270_);
                leanh::lean_ctor_set_uint8(
                    v___x_8281_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_8266_,
                );
                if v_isShared_8277_ == 0 {
                    leanh::lean_ctor_set(v___x_8276_, 0, v___x_8281_);
                    v___x_8283_ = v___x_8276_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8284_, 0, v___x_8281_);
                    v___x_8283_ = v_reuseFailAlloc_8284_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8283_;
            }
            16 => {
                if v_isShared_8289_ == 0 {
                    v___x_8291_ = v___x_8288_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8292_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8292_, 0, v_a_8286_);
                    v___x_8291_ = v_reuseFailAlloc_8292_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8291_;
            }
            18 => {
                leanh::lean_inc_ref(v_a_8300_);
                v___x_8301_ = l_Lean_Compiler_LCNF_toDecl___lam__0(
                    v_a_8300_, v_a_8149_, v_a_8150_, v_a_8151_, v_a_8152_,
                );
                if leanh::lean_obj_tag(v___x_8301_) == 0 {
                    v_a_8302_ = leanh::lean_ctor_get(v___x_8301_, 0);
                    v_isSharedCheck_8313_ = (!leanh::lean_is_exclusive(v___x_8301_)) as u8;
                    if v_isSharedCheck_8313_ == 0 {
                        v___x_8304_ = v___x_8301_;
                        v_isShared_8305_ = v_isSharedCheck_8313_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8302_);
                        leanh::lean_dec(v___x_8301_);
                        v___x_8304_ = leanh::lean_box(0);
                        v_isShared_8305_ = v_isSharedCheck_8313_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_8300_);
                    leanh::lean_dec(v___y_8298_);
                    leanh::lean_dec(v___y_8297_);
                    leanh::lean_dec_ref(v___y_8295_);
                    v_a_8314_ = leanh::lean_ctor_get(v___x_8301_, 0);
                    v_isSharedCheck_8321_ = (!leanh::lean_is_exclusive(v___x_8301_)) as u8;
                    if v_isSharedCheck_8321_ == 0 {
                        v___x_8316_ = v___x_8301_;
                        v_isShared_8317_ = v_isSharedCheck_8321_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8314_);
                        leanh::lean_dec(v___x_8301_);
                        v___x_8316_ = leanh::lean_box(0);
                        v_isShared_8317_ = v_isSharedCheck_8321_;
                        state = 21;
                        continue;
                    }
                }
            }
            19 => {
                v___x_8306_ = l_Lean_ConstantInfo_levelParams(v___y_8295_);
                leanh::lean_dec_ref(v___y_8295_);
                v___x_8307_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_8307_, 0, v___y_8297_);
                leanh::lean_ctor_set(v___x_8307_, 1, v___x_8306_);
                leanh::lean_ctor_set(v___x_8307_, 2, v_a_8300_);
                leanh::lean_ctor_set(v___x_8307_, 3, v_a_8302_);
                leanh::lean_ctor_set_uint8(
                    v___x_8307_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_8299_,
                );
                v___x_8308_ = l_Lean_Compiler_LCNF_toDecl___closed__4;
                v___x_8309_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_8309_, 0, v___x_8307_);
                leanh::lean_ctor_set(v___x_8309_, 1, v___x_8308_);
                leanh::lean_ctor_set(v___x_8309_, 2, v___y_8298_);
                leanh::lean_ctor_set_uint8(
                    v___x_8309_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_8296_,
                );
                if v_isShared_8305_ == 0 {
                    leanh::lean_ctor_set(v___x_8304_, 0, v___x_8309_);
                    v___x_8311_ = v___x_8304_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8312_, 0, v___x_8309_);
                    v___x_8311_ = v_reuseFailAlloc_8312_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_8311_;
            }
            21 => {
                if v_isShared_8317_ == 0 {
                    v___x_8319_ = v___x_8316_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_8320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8320_, 0, v_a_8314_);
                    v___x_8319_ = v_reuseFailAlloc_8320_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_8319_;
            }
            23 => {
                leanh::lean_inc(v___y_8324_);
                v___x_8325_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_8324_, v_a_8152_);
                v_a_8326_ = leanh::lean_ctor_get(v___x_8325_, 0);
                leanh::lean_inc(v_a_8326_);
                leanh::lean_dec_ref(v___x_8325_);
                if leanh::lean_obj_tag(v_a_8326_) == 1 {
                    v_val_8327_ = leanh::lean_ctor_get(v_a_8326_, 0);
                    leanh::lean_inc(v_val_8327_);
                    leanh::lean_dec_ref_known(v_a_8326_, 1);
                    leanh::lean_inc_n(v___y_8324_, 3);
                    v___x_8328_ =
                        l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_8324_, v_a_8152_);
                    v_a_8329_ = leanh::lean_ctor_get(v___x_8328_, 0);
                    leanh::lean_inc(v_a_8329_);
                    leanh::lean_dec_ref(v___x_8328_);
                    v___x_8330_ = lean_st_ref_get(v_a_8152_);
                    v_env_8331_ = leanh::lean_ctor_get(v___x_8330_, 0);
                    leanh::lean_inc_ref_n(v_env_8331_, 3);
                    leanh::lean_dec(v___x_8330_);
                    v___x_8332_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_8331_, v___y_8324_);
                    v___x_8333_ = l_Lean_getExternAttrData_x3f(v_env_8331_, v___y_8324_);
                    if leanh::lean_obj_tag(v___x_8333_) == 1 {
                        leanh::lean_dec_ref(v_env_8331_);
                        v_val_8334_ = leanh::lean_ctor_get(v___x_8333_, 0);
                        leanh::lean_inc(v_val_8334_);
                        leanh::lean_dec_ref_known(v___x_8333_, 1);
                        v___x_8335_ = 0;
                        v___x_8336_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_inlineMatchers___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_inlineMatchers___closed__7_once
                            ),
                            _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__7,
                        );
                        v___x_8337_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_inlineMatchers___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_inlineMatchers___closed__11_once
                            ),
                            _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11,
                        );
                        v___x_8338_ = lean_st_mk_ref(v___x_8337_);
                        v___x_8339_ = l_Lean_ConstantInfo_type(v_val_8327_);
                        v___x_8340_ = l_Lean_Compiler_LCNF_toLCNFType(
                            v___x_8339_,
                            v___x_8336_,
                            v___x_8338_,
                            v_a_8151_,
                            v_a_8152_,
                        );
                        if leanh::lean_obj_tag(v___x_8340_) == 0 {
                            v_a_8341_ = leanh::lean_ctor_get(v___x_8340_, 0);
                            leanh::lean_inc(v_a_8341_);
                            leanh::lean_dec_ref_known(v___x_8340_, 1);
                            v___x_8342_ = lean_st_ref_get(v___x_8338_);
                            leanh::lean_dec(v___x_8338_);
                            leanh::lean_dec(v___x_8342_);
                            v___x_8343_ = (leanh::lean_unbox(v_a_8329_) as u8);
                            leanh::lean_dec(v_a_8329_);
                            v___y_8266_ = v___x_8335_;
                            v___y_8267_ = v_val_8327_;
                            v___y_8268_ = v_val_8334_;
                            v___y_8269_ = v___y_8324_;
                            v___y_8270_ = v___x_8332_;
                            v___y_8271_ = v___x_8343_;
                            v_a_8272_ = v_a_8341_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_8338_);
                            if leanh::lean_obj_tag(v___x_8340_) == 0 {
                                v_a_8344_ = leanh::lean_ctor_get(v___x_8340_, 0);
                                leanh::lean_inc(v_a_8344_);
                                leanh::lean_dec_ref_known(v___x_8340_, 1);
                                v___x_8345_ = (leanh::lean_unbox(v_a_8329_) as u8);
                                leanh::lean_dec(v_a_8329_);
                                v___y_8266_ = v___x_8335_;
                                v___y_8267_ = v_val_8327_;
                                v___y_8268_ = v_val_8334_;
                                v___y_8269_ = v___y_8324_;
                                v___y_8270_ = v___x_8332_;
                                v___y_8271_ = v___x_8345_;
                                v_a_8272_ = v_a_8344_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_8334_);
                                leanh::lean_dec(v___x_8332_);
                                leanh::lean_dec(v_a_8329_);
                                leanh::lean_dec(v_val_8327_);
                                leanh::lean_dec(v___y_8324_);
                                v_a_8346_ = leanh::lean_ctor_get(v___x_8340_, 0);
                                v_isSharedCheck_8353_ =
                                    (!leanh::lean_is_exclusive(v___x_8340_)) as u8;
                                if v_isSharedCheck_8353_ == 0 {
                                    v___x_8348_ = v___x_8340_;
                                    v_isShared_8349_ = v_isSharedCheck_8353_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_8346_);
                                    leanh::lean_dec(v___x_8340_);
                                    v___x_8348_ = leanh::lean_box(0);
                                    v_isShared_8349_ = v_isSharedCheck_8353_;
                                    state = 24;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_8333_);
                        leanh::lean_inc(v___y_8324_);
                        leanh::lean_inc_ref(v_env_8331_);
                        v___x_8354_ = l_Lean_hasInitAttr(v_env_8331_, v___y_8324_);
                        v___x_8355_ = 1;
                        if v___x_8354_ == 0 {
                            leanh::lean_inc(v_val_8327_);
                            v___x_8356_ = l_Lean_ConstantInfo_value_x3f(v_val_8327_, v___x_8355_);
                            if leanh::lean_obj_tag(v___x_8356_) == 1 {
                                v_val_8357_ = leanh::lean_ctor_get(v___x_8356_, 0);
                                leanh::lean_inc(v_val_8357_);
                                leanh::lean_dec_ref_known(v___x_8356_, 1);
                                v___x_8358_ = 1;
                                v___x_8359_ = 0;
                                v___x_8360_ = 2;
                                v___x_8361_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    0 as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    1 as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    2 as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    3 as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    4 as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    5 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    6 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    7 as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    8 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    9 as u32,
                                    v___x_8358_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    10 as u32,
                                    v___x_8359_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    11 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    12 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    13 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    14 as u32,
                                    v___x_8360_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    15 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    16 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    17 as u32,
                                    v___x_8355_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8361_,
                                    18 as u32,
                                    v___x_8355_,
                                );
                                v___x_8362_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(
                                    v___x_8361_,
                                );
                                v___x_8363_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                                leanh::lean_ctor_set(v___x_8363_, 0, v___x_8361_);
                                leanh::lean_ctor_set_uint64(
                                    v___x_8363_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_8362_,
                                );
                                v___x_8364_ = leanh::lean_unsigned_to_nat(0);
                                v___x_8365_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_inlineMatchers___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_inlineMatchers___closed__5_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5,
                                );
                                v___x_8366_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
                                v___x_8367_ = leanh::lean_box(0);
                                v___x_8368_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                                leanh::lean_ctor_set(v___x_8368_, 0, v___x_8363_);
                                leanh::lean_ctor_set(v___x_8368_, 1, v___x_8322_);
                                leanh::lean_ctor_set(v___x_8368_, 2, v___x_8365_);
                                leanh::lean_ctor_set(v___x_8368_, 3, v___x_8366_);
                                leanh::lean_ctor_set(v___x_8368_, 4, v___x_8367_);
                                leanh::lean_ctor_set(v___x_8368_, 5, v___x_8364_);
                                leanh::lean_ctor_set(v___x_8368_, 6, v___x_8367_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_8368_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7)
                                        as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8368_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1)
                                        as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8368_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2)
                                        as u32,
                                    v___x_8354_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_8368_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3)
                                        as u32,
                                    v___x_8355_,
                                );
                                v___x_8369_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_inlineMatchers___closed__11
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_inlineMatchers___closed__11_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11,
                                );
                                v___x_8370_ = lean_st_mk_ref(v___x_8369_);
                                v___x_8371_ = l_Lean_ConstantInfo_type(v_val_8327_);
                                v___x_8372_ = l_Lean_Compiler_LCNF_toLCNFType(
                                    v___x_8371_,
                                    v___x_8368_,
                                    v___x_8370_,
                                    v_a_8151_,
                                    v_a_8152_,
                                );
                                if leanh::lean_obj_tag(v___x_8372_) == 0 {
                                    v_a_8373_ = leanh::lean_ctor_get(v___x_8372_, 0);
                                    leanh::lean_inc(v_a_8373_);
                                    leanh::lean_dec_ref_known(v___x_8372_, 1);
                                    v___x_8374_ = leanh::lean_box((v___x_8354_) as usize);
                                    v___x_8375_ = leanh::lean_box((v___x_8355_) as usize);
                                    v___f_8376_ = leanh::lean_alloc_closure(
                                        l_Lean_Compiler_LCNF_toDecl___lam__1___boxed
                                            as *mut core::ffi::c_void,
                                        9,
                                        2,
                                    );
                                    leanh::lean_closure_set(v___f_8376_, 0, v___x_8374_);
                                    leanh::lean_closure_set(v___f_8376_, 1, v___x_8375_);
                                    v___x_8377_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__2___redArg(v_val_8357_, v___f_8376_, v___x_8354_, v___x_8368_, v___x_8370_, v_a_8151_, v_a_8152_);
                                    leanh::lean_dec_ref_known(v___x_8368_, 7);
                                    if leanh::lean_obj_tag(v___x_8377_) == 0 {
                                        v_a_8378_ = leanh::lean_ctor_get(v___x_8377_, 0);
                                        leanh::lean_inc(v_a_8378_);
                                        leanh::lean_dec_ref_known(v___x_8377_, 1);
                                        v___x_8379_ = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(v_a_8378_, v_a_8151_, v_a_8152_);
                                        if leanh::lean_obj_tag(v___x_8379_) == 0 {
                                            v_a_8380_ = leanh::lean_ctor_get(v___x_8379_, 0);
                                            leanh::lean_inc(v_a_8380_);
                                            leanh::lean_dec_ref_known(v___x_8379_, 1);
                                            v___x_8381_ = l_Lean_Compiler_LCNF_macroInline(
                                                v_a_8380_, v_a_8151_, v_a_8152_,
                                            );
                                            if leanh::lean_obj_tag(v___x_8381_) == 0 {
                                                v_a_8382_ =
                                                    leanh::lean_ctor_get(v___x_8381_, 0);
                                                leanh::lean_inc(v_a_8382_);
                                                leanh::lean_dec_ref_known(v___x_8381_, 1);
                                                v___x_8383_ = l_Lean_Compiler_LCNF_inlineMatchers(
                                                    v_a_8382_, v_a_8151_, v_a_8152_,
                                                );
                                                if leanh::lean_obj_tag(v___x_8383_) == 0 {
                                                    v_a_8384_ =
                                                        leanh::lean_ctor_get(v___x_8383_, 0);
                                                    leanh::lean_inc(v_a_8384_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_8383_,
                                                        1,
                                                    );
                                                    v___x_8385_ = l_Lean_Compiler_LCNF_macroInline(
                                                        v_a_8384_, v_a_8151_, v_a_8152_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_8385_) == 0
                                                    {
                                                        v_a_8386_ = leanh::lean_ctor_get(
                                                            v___x_8385_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_8386_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_8385_,
                                                            1,
                                                        );
                                                        v___x_8387_ = lean_st_ref_get(v___x_8370_);
                                                        leanh::lean_dec(v___x_8370_);
                                                        leanh::lean_dec(v___x_8387_);
                                                        leanh::lean_inc(v_a_8373_);
                                                        v___x_8388_ =
                                                            l_Lean_Compiler_LCNF_ToLCNF_toLCNF(
                                                                v_a_8386_, v_a_8373_, v_a_8149_,
                                                                v_a_8150_, v_a_8151_, v_a_8152_,
                                                            );
                                                        if leanh::lean_obj_tag(v___x_8388_)
                                                            == 0
                                                        {
                                                            v_a_8389_ = leanh::lean_ctor_get(
                                                                v___x_8388_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_8389_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_8388_,
                                                                1,
                                                            );
                                                            if leanh::lean_obj_tag(v_a_8389_)
                                                                == 1
                                                            {
                                                                v_k_8390_ =
                                                                    leanh::lean_ctor_get(
                                                                        v_a_8389_, 1,
                                                                    );
                                                                leanh::lean_inc_ref(
                                                                    v_k_8390_,
                                                                );
                                                                if leanh::lean_obj_tag(
                                                                    v_k_8390_,
                                                                ) == 5
                                                                {
                                                                    v_decl_8391_ =
                                                                        leanh::lean_ctor_get(
                                                                            v_a_8389_, 0,
                                                                        );
                                                                    leanh::lean_inc_ref(
                                                                        v_decl_8391_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v_a_8389_, 2);
                                                                    v_isSharedCheck_8414_ = (!leanh::lean_is_exclusive(v_k_8390_)) as u8;
                                                                    if v_isSharedCheck_8414_ == 0 {
                                                                        v_unused_8415_ = leanh::lean_ctor_get(v_k_8390_, 0);
                                                                        leanh::lean_dec(
                                                                            v_unused_8415_,
                                                                        );
                                                                        v___x_8393_ = v_k_8390_;
                                                                        v_isShared_8394_ =
                                                                            v_isSharedCheck_8414_;
                                                                        state = 26;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_k_8390_,
                                                                        );
                                                                        v___x_8393_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_8394_ =
                                                                            v_isSharedCheck_8414_;
                                                                        state = 26;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_k_8390_,
                                                                    );
                                                                    v___x_8416_ =
                                                                        (leanh::lean_unbox(
                                                                            v_a_8329_,
                                                                        )
                                                                            as u8);
                                                                    leanh::lean_dec(
                                                                        v_a_8329_,
                                                                    );
                                                                    v___y_8247_ = v_val_8327_;
                                                                    v___y_8248_ = v___x_8364_;
                                                                    v___y_8249_ = v_env_8331_;
                                                                    v___y_8250_ = v___x_8354_;
                                                                    v___y_8251_ = v_a_8373_;
                                                                    v___y_8252_ = v___y_8324_;
                                                                    v___y_8253_ = v_a_8389_;
                                                                    v___y_8254_ = v___x_8332_;
                                                                    v___y_8255_ = v___x_8416_;
                                                                    v___y_8256_ = v_a_8149_;
                                                                    v___y_8257_ = v_a_8150_;
                                                                    v___y_8258_ = v_a_8151_;
                                                                    v___y_8259_ = v_a_8152_;
                                                                    state = 12;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v___x_8417_ =
                                                                    (leanh::lean_unbox(
                                                                        v_a_8329_,
                                                                    )
                                                                        as u8);
                                                                leanh::lean_dec(v_a_8329_);
                                                                v___y_8247_ = v_val_8327_;
                                                                v___y_8248_ = v___x_8364_;
                                                                v___y_8249_ = v_env_8331_;
                                                                v___y_8250_ = v___x_8354_;
                                                                v___y_8251_ = v_a_8373_;
                                                                v___y_8252_ = v___y_8324_;
                                                                v___y_8253_ = v_a_8389_;
                                                                v___y_8254_ = v___x_8332_;
                                                                v___y_8255_ = v___x_8417_;
                                                                v___y_8256_ = v_a_8149_;
                                                                v___y_8257_ = v_a_8150_;
                                                                v___y_8258_ = v_a_8151_;
                                                                v___y_8259_ = v_a_8152_;
                                                                state = 12;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_a_8373_);
                                                            leanh::lean_dec(v___x_8332_);
                                                            leanh::lean_dec_ref(v_env_8331_);
                                                            leanh::lean_dec(v_a_8329_);
                                                            leanh::lean_dec(v_val_8327_);
                                                            leanh::lean_dec(v___y_8324_);
                                                            v_a_8418_ = leanh::lean_ctor_get(
                                                                v___x_8388_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_8425_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_8388_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_8425_ == 0 {
                                                                v___x_8420_ = v___x_8388_;
                                                                v_isShared_8421_ =
                                                                    v_isSharedCheck_8425_;
                                                                state = 30;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_8418_);
                                                                leanh::lean_dec(v___x_8388_);
                                                                v___x_8420_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_8421_ =
                                                                    v_isSharedCheck_8425_;
                                                                state = 30;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_a_8373_);
                                                        leanh::lean_dec(v___x_8370_);
                                                        leanh::lean_dec(v___x_8332_);
                                                        leanh::lean_dec_ref(v_env_8331_);
                                                        leanh::lean_dec(v_a_8329_);
                                                        leanh::lean_dec(v_val_8327_);
                                                        leanh::lean_dec(v___y_8324_);
                                                        v_a_8426_ = leanh::lean_ctor_get(
                                                            v___x_8385_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_8433_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_8385_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_8433_ == 0 {
                                                            v___x_8428_ = v___x_8385_;
                                                            v_isShared_8429_ =
                                                                v_isSharedCheck_8433_;
                                                            state = 32;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_8426_);
                                                            leanh::lean_dec(v___x_8385_);
                                                            v___x_8428_ = leanh::lean_box(0);
                                                            v_isShared_8429_ =
                                                                v_isSharedCheck_8433_;
                                                            state = 32;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_a_8373_);
                                                    leanh::lean_dec(v___x_8370_);
                                                    leanh::lean_dec(v___x_8332_);
                                                    leanh::lean_dec_ref(v_env_8331_);
                                                    leanh::lean_dec(v_a_8329_);
                                                    leanh::lean_dec(v_val_8327_);
                                                    leanh::lean_dec(v___y_8324_);
                                                    v_a_8434_ =
                                                        leanh::lean_ctor_get(v___x_8383_, 0);
                                                    v_isSharedCheck_8441_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_8383_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_8441_ == 0 {
                                                        v___x_8436_ = v___x_8383_;
                                                        v_isShared_8437_ = v_isSharedCheck_8441_;
                                                        state = 34;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_8434_);
                                                        leanh::lean_dec(v___x_8383_);
                                                        v___x_8436_ = leanh::lean_box(0);
                                                        v_isShared_8437_ = v_isSharedCheck_8441_;
                                                        state = 34;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_8373_);
                                                leanh::lean_dec(v___x_8370_);
                                                leanh::lean_dec(v___x_8332_);
                                                leanh::lean_dec_ref(v_env_8331_);
                                                leanh::lean_dec(v_a_8329_);
                                                leanh::lean_dec(v_val_8327_);
                                                leanh::lean_dec(v___y_8324_);
                                                v_a_8442_ =
                                                    leanh::lean_ctor_get(v___x_8381_, 0);
                                                v_isSharedCheck_8449_ =
                                                    (!leanh::lean_is_exclusive(v___x_8381_))
                                                        as u8;
                                                if v_isSharedCheck_8449_ == 0 {
                                                    v___x_8444_ = v___x_8381_;
                                                    v_isShared_8445_ = v_isSharedCheck_8449_;
                                                    state = 36;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_8442_);
                                                    leanh::lean_dec(v___x_8381_);
                                                    v___x_8444_ = leanh::lean_box(0);
                                                    v_isShared_8445_ = v_isSharedCheck_8449_;
                                                    state = 36;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_8373_);
                                            leanh::lean_dec(v___x_8370_);
                                            leanh::lean_dec(v___x_8332_);
                                            leanh::lean_dec_ref(v_env_8331_);
                                            leanh::lean_dec(v_a_8329_);
                                            leanh::lean_dec(v_val_8327_);
                                            leanh::lean_dec(v___y_8324_);
                                            v_a_8450_ = leanh::lean_ctor_get(v___x_8379_, 0);
                                            v_isSharedCheck_8457_ =
                                                (!leanh::lean_is_exclusive(v___x_8379_))
                                                    as u8;
                                            if v_isSharedCheck_8457_ == 0 {
                                                v___x_8452_ = v___x_8379_;
                                                v_isShared_8453_ = v_isSharedCheck_8457_;
                                                state = 38;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_8450_);
                                                leanh::lean_dec(v___x_8379_);
                                                v___x_8452_ = leanh::lean_box(0);
                                                v_isShared_8453_ = v_isSharedCheck_8457_;
                                                state = 38;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_8373_);
                                        leanh::lean_dec(v___x_8370_);
                                        leanh::lean_dec(v___x_8332_);
                                        leanh::lean_dec_ref(v_env_8331_);
                                        leanh::lean_dec(v_a_8329_);
                                        leanh::lean_dec(v_val_8327_);
                                        leanh::lean_dec(v___y_8324_);
                                        v_a_8458_ = leanh::lean_ctor_get(v___x_8377_, 0);
                                        v_isSharedCheck_8465_ =
                                            (!leanh::lean_is_exclusive(v___x_8377_)) as u8;
                                        if v_isSharedCheck_8465_ == 0 {
                                            v___x_8460_ = v___x_8377_;
                                            v_isShared_8461_ = v_isSharedCheck_8465_;
                                            state = 40;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_8458_);
                                            leanh::lean_dec(v___x_8377_);
                                            v___x_8460_ = leanh::lean_box(0);
                                            v_isShared_8461_ = v_isSharedCheck_8465_;
                                            state = 40;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v___x_8370_);
                                    leanh::lean_dec_ref_known(v___x_8368_, 7);
                                    leanh::lean_dec(v_val_8357_);
                                    leanh::lean_dec(v___x_8332_);
                                    leanh::lean_dec_ref(v_env_8331_);
                                    leanh::lean_dec(v_a_8329_);
                                    leanh::lean_dec(v_val_8327_);
                                    leanh::lean_dec(v___y_8324_);
                                    v_a_8466_ = leanh::lean_ctor_get(v___x_8372_, 0);
                                    v_isSharedCheck_8473_ =
                                        (!leanh::lean_is_exclusive(v___x_8372_)) as u8;
                                    if v_isSharedCheck_8473_ == 0 {
                                        v___x_8468_ = v___x_8372_;
                                        v_isShared_8469_ = v_isSharedCheck_8473_;
                                        state = 42;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_8466_);
                                        leanh::lean_dec(v___x_8372_);
                                        v___x_8468_ = leanh::lean_box(0);
                                        v_isShared_8469_ = v_isSharedCheck_8473_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v___x_8356_);
                                leanh::lean_dec(v___x_8332_);
                                leanh::lean_dec_ref(v_env_8331_);
                                leanh::lean_dec(v_a_8329_);
                                leanh::lean_dec(v_val_8327_);
                                v___x_8474_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_toDecl___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_toDecl___closed__6_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_toDecl___closed__6,
                                );
                                v___x_8475_ =
                                    l_Lean_MessageData_ofConstName(v___y_8324_, v___x_8354_);
                                v___x_8476_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_8476_, 0, v___x_8474_);
                                leanh::lean_ctor_set(v___x_8476_, 1, v___x_8475_);
                                v___x_8477_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_toDecl___closed__8
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_toDecl___closed__8_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_toDecl___closed__8,
                                );
                                v___x_8478_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_8478_, 0, v___x_8476_);
                                leanh::lean_ctor_set(v___x_8478_, 1, v___x_8477_);
                                v___x_8479_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_8478_, v_a_8149_, v_a_8150_, v_a_8151_, v_a_8152_);
                                return v___x_8479_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_env_8331_);
                            v___x_8480_ = 0;
                            v___x_8481_ = 1;
                            v___x_8482_ = 0;
                            v___x_8483_ = 2;
                            v___x_8484_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 0 as u32, v___x_8480_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 1 as u32, v___x_8480_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 2 as u32, v___x_8480_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 3 as u32, v___x_8480_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 4 as u32, v___x_8480_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 5 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 6 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 7 as u32, v___x_8480_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 8 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 9 as u32, v___x_8481_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 10 as u32, v___x_8482_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 11 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 12 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 13 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 14 as u32, v___x_8483_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 15 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 16 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 17 as u32, v___x_8354_);
                            leanh::lean_ctor_set_uint8(v___x_8484_, 18 as u32, v___x_8354_);
                            v___x_8485_ =
                                l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_8484_);
                            v___x_8486_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                            leanh::lean_ctor_set(v___x_8486_, 0, v___x_8484_);
                            leanh::lean_ctor_set_uint64(
                                v___x_8486_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_8485_,
                            );
                            v___x_8487_ = leanh::lean_unsigned_to_nat(0);
                            v___x_8488_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_inlineMatchers___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_inlineMatchers___closed__5_once
                                ),
                                _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5,
                            );
                            v___x_8489_ = l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
                            v___x_8490_ = leanh::lean_box(0);
                            v___x_8491_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                            leanh::lean_ctor_set(v___x_8491_, 0, v___x_8486_);
                            leanh::lean_ctor_set(v___x_8491_, 1, v___x_8322_);
                            leanh::lean_ctor_set(v___x_8491_, 2, v___x_8488_);
                            leanh::lean_ctor_set(v___x_8491_, 3, v___x_8489_);
                            leanh::lean_ctor_set(v___x_8491_, 4, v___x_8490_);
                            leanh::lean_ctor_set(v___x_8491_, 5, v___x_8487_);
                            leanh::lean_ctor_set(v___x_8491_, 6, v___x_8490_);
                            leanh::lean_ctor_set_uint8(
                                v___x_8491_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                                v___x_8480_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_8491_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1)
                                    as u32,
                                v___x_8480_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_8491_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2)
                                    as u32,
                                v___x_8480_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_8491_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3)
                                    as u32,
                                v___x_8355_,
                            );
                            v___x_8492_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_inlineMatchers___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_inlineMatchers___closed__11_once
                                ),
                                _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11,
                            );
                            v___x_8493_ = lean_st_mk_ref(v___x_8492_);
                            v___x_8494_ = l_Lean_ConstantInfo_type(v_val_8327_);
                            v___x_8495_ = l_Lean_Compiler_LCNF_toLCNFType(
                                v___x_8494_,
                                v___x_8491_,
                                v___x_8493_,
                                v_a_8151_,
                                v_a_8152_,
                            );
                            leanh::lean_dec_ref_known(v___x_8491_, 7);
                            if leanh::lean_obj_tag(v___x_8495_) == 0 {
                                v_a_8496_ = leanh::lean_ctor_get(v___x_8495_, 0);
                                leanh::lean_inc(v_a_8496_);
                                leanh::lean_dec_ref_known(v___x_8495_, 1);
                                v___x_8497_ = lean_st_ref_get(v___x_8493_);
                                leanh::lean_dec(v___x_8493_);
                                leanh::lean_dec(v___x_8497_);
                                v___x_8498_ = (leanh::lean_unbox(v_a_8329_) as u8);
                                leanh::lean_dec(v_a_8329_);
                                v___y_8295_ = v_val_8327_;
                                v___y_8296_ = v___x_8480_;
                                v___y_8297_ = v___y_8324_;
                                v___y_8298_ = v___x_8332_;
                                v___y_8299_ = v___x_8498_;
                                v_a_8300_ = v_a_8496_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_8493_);
                                if leanh::lean_obj_tag(v___x_8495_) == 0 {
                                    v_a_8499_ = leanh::lean_ctor_get(v___x_8495_, 0);
                                    leanh::lean_inc(v_a_8499_);
                                    leanh::lean_dec_ref_known(v___x_8495_, 1);
                                    v___x_8500_ = (leanh::lean_unbox(v_a_8329_) as u8);
                                    leanh::lean_dec(v_a_8329_);
                                    v___y_8295_ = v_val_8327_;
                                    v___y_8296_ = v___x_8480_;
                                    v___y_8297_ = v___y_8324_;
                                    v___y_8298_ = v___x_8332_;
                                    v___y_8299_ = v___x_8500_;
                                    v_a_8300_ = v_a_8499_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_8332_);
                                    leanh::lean_dec(v_a_8329_);
                                    leanh::lean_dec(v_val_8327_);
                                    leanh::lean_dec(v___y_8324_);
                                    v_a_8501_ = leanh::lean_ctor_get(v___x_8495_, 0);
                                    v_isSharedCheck_8508_ =
                                        (!leanh::lean_is_exclusive(v___x_8495_)) as u8;
                                    if v_isSharedCheck_8508_ == 0 {
                                        v___x_8503_ = v___x_8495_;
                                        v_isShared_8504_ = v_isSharedCheck_8508_;
                                        state = 44;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_8501_);
                                        leanh::lean_dec(v___x_8495_);
                                        v___x_8503_ = leanh::lean_box(0);
                                        v_isShared_8504_ = v_isSharedCheck_8508_;
                                        state = 44;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_8326_);
                    v___x_8509_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__6_once),
                        _init_l_Lean_Compiler_LCNF_toDecl___closed__6,
                    );
                    v___x_8510_ = 0;
                    v___x_8511_ = l_Lean_MessageData_ofConstName(v___y_8324_, v___x_8510_);
                    v___x_8512_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8512_, 0, v___x_8509_);
                    leanh::lean_ctor_set(v___x_8512_, 1, v___x_8511_);
                    v___x_8513_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__10),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toDecl___closed__10_once),
                        _init_l_Lean_Compiler_LCNF_toDecl___closed__10,
                    );
                    v___x_8514_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8514_, 0, v___x_8512_);
                    leanh::lean_ctor_set(v___x_8514_, 1, v___x_8513_);
                    v___x_8515_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(
                            v___x_8514_,
                            v_a_8149_,
                            v_a_8150_,
                            v_a_8151_,
                            v_a_8152_,
                        );
                    return v___x_8515_;
                }
            }
            24 => {
                if v_isShared_8349_ == 0 {
                    v___x_8351_ = v___x_8348_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_8352_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8352_, 0, v_a_8346_);
                    v___x_8351_ = v_reuseFailAlloc_8352_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_8351_;
            }
            26 => {
                v___x_8395_ = 0;
                v___x_8396_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                    v___x_8395_,
                    v_decl_8391_,
                    v___x_8354_,
                    v_a_8150_,
                );
                if leanh::lean_obj_tag(v___x_8396_) == 0 {
                    leanh::lean_dec_ref_known(v___x_8396_, 1);
                    v_params_8397_ = leanh::lean_ctor_get(v_decl_8391_, 2);
                    leanh::lean_inc_ref(v_params_8397_);
                    v_value_8398_ = leanh::lean_ctor_get(v_decl_8391_, 4);
                    leanh::lean_inc_ref(v_value_8398_);
                    leanh::lean_dec_ref(v_decl_8391_);
                    v___x_8399_ = l_Lean_ConstantInfo_levelParams(v_val_8327_);
                    leanh::lean_dec(v_val_8327_);
                    v___x_8400_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_8400_, 0, v___y_8324_);
                    leanh::lean_ctor_set(v___x_8400_, 1, v___x_8399_);
                    leanh::lean_ctor_set(v___x_8400_, 2, v_a_8373_);
                    leanh::lean_ctor_set(v___x_8400_, 3, v_params_8397_);
                    v___x_8401_ = (leanh::lean_unbox(v_a_8329_) as u8);
                    leanh::lean_dec(v_a_8329_);
                    leanh::lean_ctor_set_uint8(
                        v___x_8400_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_8401_,
                    );
                    if v_isShared_8394_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_8393_, 0);
                        leanh::lean_ctor_set(v___x_8393_, 0, v_value_8398_);
                        v___x_8403_ = v___x_8393_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_8405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8405_, 0, v_value_8398_);
                        v___x_8403_ = v_reuseFailAlloc_8405_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8393_);
                    leanh::lean_dec_ref(v_decl_8391_);
                    leanh::lean_dec(v_a_8373_);
                    leanh::lean_dec(v___x_8332_);
                    leanh::lean_dec_ref(v_env_8331_);
                    leanh::lean_dec(v_a_8329_);
                    leanh::lean_dec(v_val_8327_);
                    leanh::lean_dec(v___y_8324_);
                    v_a_8406_ = leanh::lean_ctor_get(v___x_8396_, 0);
                    v_isSharedCheck_8413_ = (!leanh::lean_is_exclusive(v___x_8396_)) as u8;
                    if v_isSharedCheck_8413_ == 0 {
                        v___x_8408_ = v___x_8396_;
                        v_isShared_8409_ = v_isSharedCheck_8413_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8406_);
                        leanh::lean_dec(v___x_8396_);
                        v___x_8408_ = leanh::lean_box(0);
                        v_isShared_8409_ = v_isSharedCheck_8413_;
                        state = 28;
                        continue;
                    }
                }
            }
            27 => {
                v___x_8404_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_8404_, 0, v___x_8400_);
                leanh::lean_ctor_set(v___x_8404_, 1, v___x_8403_);
                leanh::lean_ctor_set(v___x_8404_, 2, v___x_8332_);
                leanh::lean_ctor_set_uint8(
                    v___x_8404_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_8354_,
                );
                v___y_8195_ = v___x_8364_;
                v___y_8196_ = v_env_8331_;
                v___y_8197_ = v___x_8354_;
                v_decl_8198_ = v___x_8404_;
                v___y_8199_ = v_a_8149_;
                v___y_8200_ = v_a_8150_;
                v___y_8201_ = v_a_8151_;
                v___y_8202_ = v_a_8152_;
                state = 5;
                continue;
            }
            28 => {
                if v_isShared_8409_ == 0 {
                    v___x_8411_ = v___x_8408_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_8412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8412_, 0, v_a_8406_);
                    v___x_8411_ = v_reuseFailAlloc_8412_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_8411_;
            }
            30 => {
                if v_isShared_8421_ == 0 {
                    v___x_8423_ = v___x_8420_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_8424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 0, v_a_8418_);
                    v___x_8423_ = v_reuseFailAlloc_8424_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_8423_;
            }
            32 => {
                if v_isShared_8429_ == 0 {
                    v___x_8431_ = v___x_8428_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_8432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8432_, 0, v_a_8426_);
                    v___x_8431_ = v_reuseFailAlloc_8432_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_8431_;
            }
            34 => {
                if v_isShared_8437_ == 0 {
                    v___x_8439_ = v___x_8436_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_8440_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8440_, 0, v_a_8434_);
                    v___x_8439_ = v_reuseFailAlloc_8440_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_8439_;
            }
            36 => {
                if v_isShared_8445_ == 0 {
                    v___x_8447_ = v___x_8444_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_8448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8448_, 0, v_a_8442_);
                    v___x_8447_ = v_reuseFailAlloc_8448_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_8447_;
            }
            38 => {
                if v_isShared_8453_ == 0 {
                    v___x_8455_ = v___x_8452_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_8456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8456_, 0, v_a_8450_);
                    v___x_8455_ = v_reuseFailAlloc_8456_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_8455_;
            }
            40 => {
                if v_isShared_8461_ == 0 {
                    v___x_8463_ = v___x_8460_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_8464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8464_, 0, v_a_8458_);
                    v___x_8463_ = v_reuseFailAlloc_8464_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_8463_;
            }
            42 => {
                if v_isShared_8469_ == 0 {
                    v___x_8471_ = v___x_8468_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_8472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8472_, 0, v_a_8466_);
                    v___x_8471_ = v_reuseFailAlloc_8472_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_8471_;
            }
            44 => {
                if v_isShared_8504_ == 0 {
                    v___x_8506_ = v___x_8503_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_8507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8507_, 0, v_a_8501_);
                    v___x_8506_ = v_reuseFailAlloc_8507_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_8506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_toDecl___boxed(
    mut v_declName_8518_: *mut leanh::LeanObject,
    mut v_a_8519_: *mut leanh::LeanObject,
    mut v_a_8520_: *mut leanh::LeanObject,
    mut v_a_8521_: *mut leanh::LeanObject,
    mut v_a_8522_: *mut leanh::LeanObject,
    mut v_a_8523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8524_ =
        l_Lean_Compiler_LCNF_toDecl(v_declName_8518_, v_a_8519_, v_a_8520_, v_a_8521_, v_a_8522_);
    leanh::lean_dec(v_a_8522_);
    leanh::lean_dec_ref(v_a_8521_);
    leanh::lean_dec(v_a_8520_);
    leanh::lean_dec_ref(v_a_8519_);
    return v_res_8524_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(
    mut v___x_8525_: u8,
    mut v_inst_8526_: *mut leanh::LeanObject,
    mut v_a_8527_: *mut leanh::LeanObject,
    mut v___y_8528_: *mut leanh::LeanObject,
    mut v___y_8529_: *mut leanh::LeanObject,
    mut v___y_8530_: *mut leanh::LeanObject,
    mut v___y_8531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8533_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(
            v___x_8525_,
            v_a_8527_,
            v___y_8528_,
            v___y_8529_,
            v___y_8530_,
            v___y_8531_,
        );
    return v___x_8533_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(
    mut v___x_8534_: *mut leanh::LeanObject,
    mut v_inst_8535_: *mut leanh::LeanObject,
    mut v_a_8536_: *mut leanh::LeanObject,
    mut v___y_8537_: *mut leanh::LeanObject,
    mut v___y_8538_: *mut leanh::LeanObject,
    mut v___y_8539_: *mut leanh::LeanObject,
    mut v___y_8540_: *mut leanh::LeanObject,
    mut v___y_8541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_16465__boxed_8542_: u8 = 0;
    let mut v_res_8543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_16465__boxed_8542_ = (leanh::lean_unbox(v___x_8534_) as u8);
    v_res_8543_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(
            v___x_16465__boxed_8542_,
            v_inst_8535_,
            v_a_8536_,
            v___y_8537_,
            v___y_8538_,
            v___y_8539_,
            v___y_8540_,
        );
    leanh::lean_dec(v___y_8540_);
    leanh::lean_dec_ref(v___y_8539_);
    leanh::lean_dec(v___y_8538_);
    leanh::lean_dec_ref(v___y_8537_);
    return v_res_8543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(
    mut v___x_8544_: u8,
    mut v_sz_8545_: usize,
    mut v_i_8546_: usize,
    mut v_bs_8547_: *mut leanh::LeanObject,
    mut v___y_8548_: *mut leanh::LeanObject,
    mut v___y_8549_: *mut leanh::LeanObject,
    mut v___y_8550_: *mut leanh::LeanObject,
    mut v___y_8551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_8544_, v_sz_8545_, v_i_8546_, v_bs_8547_, v___y_8549_);
    return v___x_8553_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(
    mut v___x_8554_: *mut leanh::LeanObject,
    mut v_sz_8555_: *mut leanh::LeanObject,
    mut v_i_8556_: *mut leanh::LeanObject,
    mut v_bs_8557_: *mut leanh::LeanObject,
    mut v___y_8558_: *mut leanh::LeanObject,
    mut v___y_8559_: *mut leanh::LeanObject,
    mut v___y_8560_: *mut leanh::LeanObject,
    mut v___y_8561_: *mut leanh::LeanObject,
    mut v___y_8562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_16488__boxed_8563_: u8 = 0;
    let mut v_sz_boxed_8564_: usize = 0;
    let mut v_i_boxed_8565_: usize = 0;
    let mut v_res_8566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_16488__boxed_8563_ = (leanh::lean_unbox(v___x_8554_) as u8);
    v_sz_boxed_8564_ = leanh::lean_unbox_usize(v_sz_8555_);
    leanh::lean_dec(v_sz_8555_);
    v_i_boxed_8565_ = leanh::lean_unbox_usize(v_i_8556_);
    leanh::lean_dec(v_i_8556_);
    v_res_8566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_16488__boxed_8563_, v_sz_boxed_8564_, v_i_boxed_8565_, v_bs_8557_, v___y_8558_, v___y_8559_, v___y_8560_, v___y_8561_);
    leanh::lean_dec(v___y_8561_);
    leanh::lean_dec_ref(v___y_8560_);
    leanh::lean_dec(v___y_8559_);
    leanh::lean_dec_ref(v___y_8558_);
    return v_res_8566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ToDecl(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ToDecl(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ToDecl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_ExportAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ToDecl(builtin);
}