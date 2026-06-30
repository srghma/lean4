// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Attr
// Imports: Lean.Meta.Tactic.Simp Std.Tactic.Do.Syntax Init.While Init.Syntax
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_expr_eqv, lean_infer_type, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_of_nat,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_structEq;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_node2, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArg, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Attributes::{
    l_Lean_TagAttribute_hasTag, l_Lean_getAttrParamOptPrio, l_Lean_getBuiltinAttributeImpl,
    l_Lean_registerBuiltinAttribute, l_Lean_registerTagAttribute,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_levelParams;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_beta, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppFn_x27, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21,
    l_Lean_Expr_hasExprMVar, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_isMVar, l_Lean_instBEqFVarId_beq,
    l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_type;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp,
    l_Lean_FVarId_findDecl_x3f___redArg, l_Lean_Meta_Config_toConfigWithKey,
    l_Lean_Meta_forallMetaTelescope, l_Lean_Meta_forallMetaTelescopeReducing,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_empty, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Main::l_Lean_Meta_DiscrTree_mkPath;
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::{
    l_Lean_Meta_Simp_Context_mkDefault___redArg, l_Lean_Meta_registerSimpAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simp;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpExtension_getTheorems___redArg, l_Lean_Meta_simpGlobalConfig,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::{
    initialize_Lean_Meta_Tactic_Simp, runtime_initialize_Lean_Meta_Tactic_Simp,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 112, 101, 99, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17186385980065365684 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6272605754531080404 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8329279028482663286 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5409699204079762053 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14659826576719934041 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18416200079748401721 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5290553688444538652 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1661666541244903741 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15779238732938891787 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2811310707656781194 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8663997493493226818 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 112, 101, 99, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10914722979873168125 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17038327469269433204 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6906709583315380253 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4219124626137388200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4322195018672482898 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9557857920321765335 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3768395763851350643 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10035844726815915179 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1315642830 as usize) << 1) | 1) as *mut leanh::LeanObject,5914060295816363643 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10159048236521340864 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6137995315809427492 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,15422401092800951869 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 118, 99, 103, 101, 110, 95, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12870045445243962497 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 105, 110, 116, 101, 114, 110, 97, 108, 108, 121, 32, 117, 115, 101, 100, 32, 98, 121, 32, 96, 109, 118, 99, 103, 101, 110, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 118, 99, 103, 101, 110, 83, 105, 109, 112, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8359407510875696518 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6847237493982576655 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0: u64 = 0;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 103, 108, 111, 98, 97, 108, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
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
        83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 108, 111, 99, 97, 108, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
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
        83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 115, 116, 120, 32, 95, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_value) as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8614124190858717794 as *mut leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 105, 110, 100, 32, 111, 102, 32, 115, 112, 101, 99, 32, 116, 104, 101, 111, 114, 101, 109, 59, 32, 110, 111, 116, 32, 97, 32, 116, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value) as *mut leanh::LeanObject,11963640885769744415 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 111, 115, 116, 83, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 114, 103, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value) as *mut leanh::LeanObject,6471916472876379905 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value) as *mut leanh::LeanObject,16115802990853135195 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 39, 115, 112, 101, 99, 39, 44, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 39, 115, 112, 101, 99, 39, 44, 32, 108, 111, 99, 97,
        108, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 112, 101, 99, 77, 97, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value)
            as *mut leanh::LeanObject,
        14904224527309176076 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_specAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value:
    leanh::LeanStringObject<83> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 83,
    m_capacity: 83,
    m_length: 82,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 39, 115, 112, 101, 99, 39, 58, 32, 116, 97, 114, 103,
        101, 116, 32, 119, 97, 115, 32, 110, 101, 105, 116, 104, 101, 114, 32, 97, 32, 72, 111, 97,
        114, 101, 32, 116, 114, 105, 112, 108, 101, 32, 115, 112, 101, 99, 105, 102, 105, 99, 97,
        116, 105, 111, 110, 32, 110, 111, 114, 32, 97, 32, 39, 115, 105, 109, 112, 39, 32, 108,
        101, 109, 109, 97, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1: u64 = 0;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6_value:
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        82, 101, 97, 115, 111, 110, 32, 102, 111, 114, 32, 102, 97, 105, 108, 117, 114, 101, 32,
        116, 111, 32, 97, 112, 112, 108, 121, 32, 115, 112, 101, 99, 32, 97, 116, 116, 114, 105,
        98, 117, 116, 101, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 105, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [109, 107, 83, 112, 101, 99, 65, 116, 116, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8359407510875696518 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_4)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value)
            as *mut leanh::LeanObject,
        11196778731259658883 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 112, 101, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value)
            as *mut leanh::LeanObject,
        9363898782269073664 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value:
    leanh::LeanStringObject<97> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 97,
    m_capacity: 97,
    m_length: 96,
    m_data: [
        77, 97, 114, 107, 115, 32, 72, 111, 97, 114, 101, 32, 116, 114, 105, 112, 108, 101, 32,
        115, 112, 101, 99, 105, 102, 105, 99, 97, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32,
        115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 116, 111, 32, 117, 115,
        101, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 96, 109, 115, 112, 101, 99, 96, 32, 97,
        110, 100, 32, 96, 109, 118, 99, 103, 101, 110, 96, 32, 116, 97, 99, 116, 105, 99, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value)
            as *mut leanh::LeanObject,
        1 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [115, 112, 101, 99, 95, 105, 110, 118, 97, 114, 105, 97, 110, 116, 95, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5551193628827022521 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: leanh::LeanStringObject<58> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [109, 97, 114, 107, 115, 32, 97, 32, 116, 121, 112, 101, 32, 97, 115, 32, 97, 110, 32, 105, 110, 118, 97, 114, 105, 97, 110, 116, 32, 116, 121, 112, 101, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 109, 118, 99, 103, 101, 110, 96, 32, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [115, 112, 101, 99, 73, 110, 118, 97, 114, 105, 97, 110, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8359407510875696518 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10016391191665048052 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_3593_ = 0;
    v___x_3594_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_3595_ = l_Lean_registerTraceClass(v___x_3592_, v___x_3593_, v___x_3594_);
    return v___x_3595_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2____boxed(
    mut v_a_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
    return v_res_3597_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3611_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_3612_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_3613_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_3614_ = l_Lean_Meta_registerSimpAttr(v___x_3611_, v___x_3612_, v___x_3613_);
    return v___x_3614_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2____boxed(
    mut v_a_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
    return v_res_3616_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(
    mut v_a_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt;
    v___x_3620_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3619_, v_a_3617_);
    return v___x_3620_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg___boxed(
    mut v_a_3621_: *mut leanh::LeanObject,
    mut v_a_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3623_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(v_a_3621_);
    leanh::lean_dec(v_a_3621_);
    return v_res_3623_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(
    mut v_a_3624_: *mut leanh::LeanObject,
    mut v_a_3625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(v_a_3625_);
    return v___x_3627_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed(
    mut v_a_3628_: *mut leanh::LeanObject,
    mut v_a_3629_: *mut leanh::LeanObject,
    mut v_a_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(v_a_3628_, v_a_3629_);
    leanh::lean_dec(v_a_3629_);
    leanh::lean_dec_ref(v_a_3628_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(
    mut v_x_3632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3632_) {
        0 => {
            let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3633_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3633_;
        }
        1 => {
            let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3634_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3634_;
        }
        _ => {
            let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3635_ = leanh::lean_unsigned_to_nat(2);
            return v___x_3635_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx___boxed(
    mut v_x_3636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3637_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(v_x_3636_);
    leanh::lean_dec_ref(v_x_3636_);
    return v_res_3637_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(
    mut v_t_3638_: *mut leanh::LeanObject,
    mut v_k_3639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_3638_) == 2 {
        let mut v_id_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_proof_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_id_3640_ = leanh::lean_ctor_get(v_t_3638_, 0);
        leanh::lean_inc(v_id_3640_);
        v_ref_3641_ = leanh::lean_ctor_get(v_t_3638_, 1);
        leanh::lean_inc(v_ref_3641_);
        v_proof_3642_ = leanh::lean_ctor_get(v_t_3638_, 2);
        leanh::lean_inc_ref(v_proof_3642_);
        leanh::lean_dec_ref_known(v_t_3638_, 3);
        v___x_3643_ = leanh::lean_apply_3(v_k_3639_, v_id_3640_, v_ref_3641_, v_proof_3642_);
        return v___x_3643_;
    } else {
        let mut v_declName_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_3644_ = leanh::lean_ctor_get(v_t_3638_, 0);
        leanh::lean_inc(v_declName_3644_);
        leanh::lean_dec_ref(v_t_3638_);
        v___x_3645_ = leanh::lean_apply_1(v_k_3639_, v_declName_3644_);
        return v___x_3645_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(
    mut v_motive_3646_: *mut leanh::LeanObject,
    mut v_ctorIdx_3647_: *mut leanh::LeanObject,
    mut v_t_3648_: *mut leanh::LeanObject,
    mut v_h_3649_: *mut leanh::LeanObject,
    mut v_k_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3651_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3648_, v_k_3650_);
    return v___x_3651_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___boxed(
    mut v_motive_3652_: *mut leanh::LeanObject,
    mut v_ctorIdx_3653_: *mut leanh::LeanObject,
    mut v_t_3654_: *mut leanh::LeanObject,
    mut v_h_3655_: *mut leanh::LeanObject,
    mut v_k_3656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(
        v_motive_3652_,
        v_ctorIdx_3653_,
        v_t_3654_,
        v_h_3655_,
        v_k_3656_,
    );
    leanh::lean_dec(v_ctorIdx_3653_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim___redArg(
    mut v_t_3658_: *mut leanh::LeanObject,
    mut v_global_3659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3660_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3658_, v_global_3659_);
    return v___x_3660_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim(
    mut v_motive_3661_: *mut leanh::LeanObject,
    mut v_t_3662_: *mut leanh::LeanObject,
    mut v_h_3663_: *mut leanh::LeanObject,
    mut v_global_3664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3662_, v_global_3664_);
    return v___x_3665_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim___redArg(
    mut v_t_3666_: *mut leanh::LeanObject,
    mut v_local_3667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3668_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3666_, v_local_3667_);
    return v___x_3668_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim(
    mut v_motive_3669_: *mut leanh::LeanObject,
    mut v_t_3670_: *mut leanh::LeanObject,
    mut v_h_3671_: *mut leanh::LeanObject,
    mut v_local_3672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3670_, v_local_3672_);
    return v___x_3673_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim___redArg(
    mut v_t_3674_: *mut leanh::LeanObject,
    mut v_stx_3675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3676_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3674_, v_stx_3675_);
    return v___x_3676_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim(
    mut v_motive_3677_: *mut leanh::LeanObject,
    mut v_t_3678_: *mut leanh::LeanObject,
    mut v_h_3679_: *mut leanh::LeanObject,
    mut v_stx_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3681_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3678_, v_stx_3680_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
    mut v_x_3686_: *mut leanh::LeanObject,
    mut v_x_3687_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_3686_) {
        0 => {
            if leanh::lean_obj_tag(v_x_3687_) == 0 {
                let mut v_declName_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_declName_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3690_: u8 = 0;
                v_declName_3688_ = leanh::lean_ctor_get(v_x_3686_, 0);
                leanh::lean_inc(v_declName_3688_);
                leanh::lean_dec_ref_known(v_x_3686_, 1);
                v_declName_3689_ = leanh::lean_ctor_get(v_x_3687_, 0);
                leanh::lean_inc(v_declName_3689_);
                leanh::lean_dec_ref_known(v_x_3687_, 1);
                v___x_3690_ = lean_name_eq(v_declName_3688_, v_declName_3689_);
                leanh::lean_dec(v_declName_3689_);
                leanh::lean_dec(v_declName_3688_);
                return v___x_3690_;
            } else {
                let mut v___x_3691_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_3686_, 1);
                leanh::lean_dec_ref(v_x_3687_);
                v___x_3691_ = 0;
                return v___x_3691_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_3687_) == 1 {
                let mut v_fvarId_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_fvarId_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3694_: u8 = 0;
                v_fvarId_3692_ = leanh::lean_ctor_get(v_x_3686_, 0);
                leanh::lean_inc(v_fvarId_3692_);
                leanh::lean_dec_ref_known(v_x_3686_, 1);
                v_fvarId_3693_ = leanh::lean_ctor_get(v_x_3687_, 0);
                leanh::lean_inc(v_fvarId_3693_);
                leanh::lean_dec_ref_known(v_x_3687_, 1);
                v___x_3694_ = l_Lean_instBEqFVarId_beq(v_fvarId_3692_, v_fvarId_3693_);
                leanh::lean_dec(v_fvarId_3693_);
                leanh::lean_dec(v_fvarId_3692_);
                return v___x_3694_;
            } else {
                let mut v___x_3695_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_3686_, 1);
                leanh::lean_dec_ref(v_x_3687_);
                v___x_3695_ = 0;
                return v___x_3695_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_3687_) == 2 {
                let mut v_id_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_proof_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_proof_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3702_: u8 = 0;
                v_id_3696_ = leanh::lean_ctor_get(v_x_3686_, 0);
                leanh::lean_inc(v_id_3696_);
                v_ref_3697_ = leanh::lean_ctor_get(v_x_3686_, 1);
                leanh::lean_inc(v_ref_3697_);
                v_proof_3698_ = leanh::lean_ctor_get(v_x_3686_, 2);
                leanh::lean_inc_ref(v_proof_3698_);
                leanh::lean_dec_ref_known(v_x_3686_, 3);
                v_id_3699_ = leanh::lean_ctor_get(v_x_3687_, 0);
                leanh::lean_inc(v_id_3699_);
                v_ref_3700_ = leanh::lean_ctor_get(v_x_3687_, 1);
                leanh::lean_inc(v_ref_3700_);
                v_proof_3701_ = leanh::lean_ctor_get(v_x_3687_, 2);
                leanh::lean_inc_ref(v_proof_3701_);
                leanh::lean_dec_ref_known(v_x_3687_, 3);
                v___x_3702_ = lean_name_eq(v_id_3696_, v_id_3699_);
                leanh::lean_dec(v_id_3699_);
                leanh::lean_dec(v_id_3696_);
                if v___x_3702_ == 0 {
                    leanh::lean_dec_ref(v_proof_3701_);
                    leanh::lean_dec(v_ref_3700_);
                    leanh::lean_dec_ref(v_proof_3698_);
                    leanh::lean_dec(v_ref_3697_);
                    return v___x_3702_;
                } else {
                    let mut v___x_3703_: u8 = 0;
                    v___x_3703_ = l_Lean_Syntax_structEq(v_ref_3697_, v_ref_3700_);
                    if v___x_3703_ == 0 {
                        leanh::lean_dec_ref(v_proof_3701_);
                        leanh::lean_dec_ref(v_proof_3698_);
                        return v___x_3703_;
                    } else {
                        let mut v___x_3704_: u8 = 0;
                        v___x_3704_ = lean_expr_eqv(v_proof_3698_, v_proof_3701_);
                        leanh::lean_dec_ref(v_proof_3701_);
                        leanh::lean_dec_ref(v_proof_3698_);
                        return v___x_3704_;
                    }
                }
            } else {
                let mut v___x_3705_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_3686_, 3);
                leanh::lean_dec_ref(v_x_3687_);
                v___x_3705_ = 0;
                return v___x_3705_;
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed(
    mut v_x_3706_: *mut leanh::LeanObject,
    mut v_x_3707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3708_: u8 = 0;
    let mut v_r_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_3706_, v_x_3707_);
    v_r_3709_ = leanh::lean_box((v_res_3708_) as usize);
    return v_r_3709_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(
    mut v_x_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_declName_3713_ = leanh::lean_ctor_get(v_x_3712_, 0);
    leanh::lean_inc(v_declName_3713_);
    return v_declName_3713_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key___boxed(
    mut v_x_3714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3715_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_3714_);
    leanh::lean_dec_ref(v_x_3714_);
    return v_res_3715_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(
    mut v_x_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3716_) {
                0 => {
                    v_declName_3717_ = leanh::lean_ctor_get(v_x_3716_, 0);
                    leanh::lean_inc(v_declName_3717_);
                    leanh::lean_dec_ref_known(v_x_3716_, 1);
                    v___x_3718_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3718_, 0, v_declName_3717_);
                    v___x_3719_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3719_, 0, v___x_3718_);
                    return v___x_3719_;
                }
                1 => {
                    v_fvarId_3720_ = leanh::lean_ctor_get(v_x_3716_, 0);
                    v_isSharedCheck_3728_ = (!leanh::lean_is_exclusive(v_x_3716_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3722_ = v_x_3716_;
                        v_isShared_3723_ = v_isSharedCheck_3728_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_3720_);
                        leanh::lean_dec(v_x_3716_);
                        v___x_3722_ = leanh::lean_box(0);
                        v_isShared_3723_ = v_isSharedCheck_3728_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_x_3716_);
                    v___x_3729_ = leanh::lean_box(0);
                    return v___x_3729_;
                }
            },
            1 => {
                if v_isShared_3723_ == 0 {
                    v___x_3725_ = v___x_3722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_fvarId_3720_);
                    v___x_3725_ = v_reuseFailAlloc_3727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3726_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3726_, 0, v___x_3725_);
                return v___x_3726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3730_) == 0 {
                    v___x_3732_ = l_List_reverse___redArg(v_a_3731_);
                    return v___x_3732_;
                } else {
                    v_head_3733_ = leanh::lean_ctor_get(v_a_3730_, 0);
                    v_tail_3734_ = leanh::lean_ctor_get(v_a_3730_, 1);
                    v_isSharedCheck_3743_ = (!leanh::lean_is_exclusive(v_a_3730_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3736_ = v_a_3730_;
                        v_isShared_3737_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3734_);
                        leanh::lean_inc(v_head_3733_);
                        leanh::lean_dec(v_a_3730_);
                        v___x_3736_ = leanh::lean_box(0);
                        v_isShared_3737_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3738_ = l_Lean_mkLevelParam(v_head_3733_);
                if v_isShared_3737_ == 0 {
                    leanh::lean_ctor_set(v___x_3736_, 1, v_a_3731_);
                    leanh::lean_ctor_set(v___x_3736_, 0, v___x_3738_);
                    v___x_3740_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_a_3731_);
                    v___x_3740_ = v_reuseFailAlloc_3742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3730_ = v_tail_3734_;
                v_a_3731_ = v___x_3740_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(
    mut v_msgData_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = lean_st_ref_get(v___y_3748_);
    v_env_3751_ = leanh::lean_ctor_get(v___x_3750_, 0);
    leanh::lean_inc_ref(v_env_3751_);
    leanh::lean_dec(v___x_3750_);
    v___x_3752_ = lean_st_ref_get(v___y_3746_);
    v_mctx_3753_ = leanh::lean_ctor_get(v___x_3752_, 0);
    leanh::lean_inc_ref(v_mctx_3753_);
    leanh::lean_dec(v___x_3752_);
    v_lctx_3754_ = leanh::lean_ctor_get(v___y_3745_, 2);
    v_options_3755_ = leanh::lean_ctor_get(v___y_3747_, 2);
    leanh::lean_inc_ref(v_options_3755_);
    leanh::lean_inc_ref(v_lctx_3754_);
    v___x_3756_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3756_, 0, v_env_3751_);
    leanh::lean_ctor_set(v___x_3756_, 1, v_mctx_3753_);
    leanh::lean_ctor_set(v___x_3756_, 2, v_lctx_3754_);
    leanh::lean_ctor_set(v___x_3756_, 3, v_options_3755_);
    v___x_3757_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3757_, 0, v___x_3756_);
    leanh::lean_ctor_set(v___x_3757_, 1, v_msgData_3744_);
    v___x_3758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3758_, 0, v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msgData_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
    leanh::lean_dec(v___y_3763_);
    leanh::lean_dec_ref(v___y_3762_);
    leanh::lean_dec(v___y_3761_);
    leanh::lean_dec_ref(v___y_3760_);
    return v_res_3765_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(
    mut v_msg_3766_: *mut leanh::LeanObject,
    mut v___y_3767_: *mut leanh::LeanObject,
    mut v___y_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3772_ = leanh::lean_ctor_get(v___y_3769_, 5);
                v___x_3773_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
                v_a_3774_ = leanh::lean_ctor_get(v___x_3773_, 0);
                v_isSharedCheck_3782_ = (!leanh::lean_is_exclusive(v___x_3773_)) as u8;
                if v_isSharedCheck_3782_ == 0 {
                    v___x_3776_ = v___x_3773_;
                    v_isShared_3777_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3774_);
                    leanh::lean_dec(v___x_3773_);
                    v___x_3776_ = leanh::lean_box(0);
                    v_isShared_3777_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3772_);
                v___x_3778_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3778_, 0, v_ref_3772_);
                leanh::lean_ctor_set(v___x_3778_, 1, v_a_3774_);
                if v_isShared_3777_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3776_, 1);
                    leanh::lean_ctor_set(v___x_3776_, 0, v___x_3778_);
                    v___x_3780_ = v___x_3776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
                    v___x_3780_ = v_reuseFailAlloc_3781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_msg_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
    mut v___y_3787_: *mut leanh::LeanObject,
    mut v___y_3788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
    leanh::lean_dec(v___y_3787_);
    leanh::lean_dec_ref(v___y_3786_);
    leanh::lean_dec(v___y_3785_);
    leanh::lean_dec_ref(v___y_3784_);
    return v_res_3789_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_ref_3790_: *mut leanh::LeanObject,
    mut v_msg_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
    mut v___y_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3809_: u8 = 0;
    let mut v_cancelTk_x3f_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3811_: u8 = 0;
    let mut v_inheritedTraceOptions_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3797_ = leanh::lean_ctor_get(v___y_3794_, 0);
    v_fileMap_3798_ = leanh::lean_ctor_get(v___y_3794_, 1);
    v_options_3799_ = leanh::lean_ctor_get(v___y_3794_, 2);
    v_currRecDepth_3800_ = leanh::lean_ctor_get(v___y_3794_, 3);
    v_maxRecDepth_3801_ = leanh::lean_ctor_get(v___y_3794_, 4);
    v_ref_3802_ = leanh::lean_ctor_get(v___y_3794_, 5);
    v_currNamespace_3803_ = leanh::lean_ctor_get(v___y_3794_, 6);
    v_openDecls_3804_ = leanh::lean_ctor_get(v___y_3794_, 7);
    v_initHeartbeats_3805_ = leanh::lean_ctor_get(v___y_3794_, 8);
    v_maxHeartbeats_3806_ = leanh::lean_ctor_get(v___y_3794_, 9);
    v_quotContext_3807_ = leanh::lean_ctor_get(v___y_3794_, 10);
    v_currMacroScope_3808_ = leanh::lean_ctor_get(v___y_3794_, 11);
    v_diag_3809_ = leanh::lean_ctor_get_uint8(
        v___y_3794_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3810_ = leanh::lean_ctor_get(v___y_3794_, 12);
    v_suppressElabErrors_3811_ = leanh::lean_ctor_get_uint8(
        v___y_3794_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3812_ = leanh::lean_ctor_get(v___y_3794_, 13);
    v_ref_3813_ = l_Lean_replaceRef(v_ref_3790_, v_ref_3802_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3812_);
    leanh::lean_inc(v_cancelTk_x3f_3810_);
    leanh::lean_inc(v_currMacroScope_3808_);
    leanh::lean_inc(v_quotContext_3807_);
    leanh::lean_inc(v_maxHeartbeats_3806_);
    leanh::lean_inc(v_initHeartbeats_3805_);
    leanh::lean_inc(v_openDecls_3804_);
    leanh::lean_inc(v_currNamespace_3803_);
    leanh::lean_inc(v_maxRecDepth_3801_);
    leanh::lean_inc(v_currRecDepth_3800_);
    leanh::lean_inc_ref(v_options_3799_);
    leanh::lean_inc_ref(v_fileMap_3798_);
    leanh::lean_inc_ref(v_fileName_3797_);
    v___x_3814_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3814_, 0, v_fileName_3797_);
    leanh::lean_ctor_set(v___x_3814_, 1, v_fileMap_3798_);
    leanh::lean_ctor_set(v___x_3814_, 2, v_options_3799_);
    leanh::lean_ctor_set(v___x_3814_, 3, v_currRecDepth_3800_);
    leanh::lean_ctor_set(v___x_3814_, 4, v_maxRecDepth_3801_);
    leanh::lean_ctor_set(v___x_3814_, 5, v_ref_3813_);
    leanh::lean_ctor_set(v___x_3814_, 6, v_currNamespace_3803_);
    leanh::lean_ctor_set(v___x_3814_, 7, v_openDecls_3804_);
    leanh::lean_ctor_set(v___x_3814_, 8, v_initHeartbeats_3805_);
    leanh::lean_ctor_set(v___x_3814_, 9, v_maxHeartbeats_3806_);
    leanh::lean_ctor_set(v___x_3814_, 10, v_quotContext_3807_);
    leanh::lean_ctor_set(v___x_3814_, 11, v_currMacroScope_3808_);
    leanh::lean_ctor_set(v___x_3814_, 12, v_cancelTk_x3f_3810_);
    leanh::lean_ctor_set(v___x_3814_, 13, v_inheritedTraceOptions_3812_);
    leanh::lean_ctor_set_uint8(
        v___x_3814_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3809_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3814_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3811_,
    );
    v___x_3815_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_3791_, v___y_3792_, v___y_3793_, v___x_3814_, v___y_3795_);
    leanh::lean_dec_ref_known(v___x_3814_, 14);
    return v___x_3815_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_ref_3816_: *mut leanh::LeanObject,
    mut v_msg_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
    mut v___y_3821_: *mut leanh::LeanObject,
    mut v___y_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3816_, v_msg_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
    leanh::lean_dec(v___y_3821_);
    leanh::lean_dec_ref(v___y_3820_);
    leanh::lean_dec(v___y_3819_);
    leanh::lean_dec_ref(v___y_3818_);
    leanh::lean_dec(v_ref_3816_);
    return v_res_3823_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3824_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_3826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3826_, 0, v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3828_ = leanh::lean_unsigned_to_nat(0);
    v___x_3829_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3829_, 0, v___x_3828_);
    leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
    leanh::lean_ctor_set(v___x_3829_, 2, v___x_3828_);
    leanh::lean_ctor_set(v___x_3829_, 3, v___x_3828_);
    leanh::lean_ctor_set(v___x_3829_, 4, v___x_3827_);
    leanh::lean_ctor_set(v___x_3829_, 5, v___x_3827_);
    leanh::lean_ctor_set(v___x_3829_, 6, v___x_3827_);
    leanh::lean_ctor_set(v___x_3829_, 7, v___x_3827_);
    leanh::lean_ctor_set(v___x_3829_, 8, v___x_3827_);
    leanh::lean_ctor_set(v___x_3829_, 9, v___x_3827_);
    return v___x_3829_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = leanh::lean_unsigned_to_nat(32);
    v___x_3831_ = lean_mk_empty_array_with_capacity(v___x_3830_);
    v___x_3832_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3832_, 0, v___x_3831_);
    return v___x_3832_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3833_: usize = 0;
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = 5usize;
    v___x_3834_ = leanh::lean_unsigned_to_nat(0);
    v___x_3835_ = leanh::lean_unsigned_to_nat(32);
    v___x_3836_ = lean_mk_empty_array_with_capacity(v___x_3835_);
    v___x_3837_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_3838_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3838_, 0, v___x_3837_);
    leanh::lean_ctor_set(v___x_3838_, 1, v___x_3836_);
    leanh::lean_ctor_set(v___x_3838_, 2, v___x_3834_);
    leanh::lean_ctor_set(v___x_3838_, 3, v___x_3834_);
    leanh::lean_ctor_set_usize(v___x_3838_, 4, v___x_3833_);
    return v___x_3838_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = leanh::lean_box(1);
    v___x_3840_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_3841_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3842_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3842_, 0, v___x_3841_);
    leanh::lean_ctor_set(v___x_3842_, 1, v___x_3840_);
    leanh::lean_ctor_set(v___x_3842_, 2, v___x_3839_);
    return v___x_3842_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_3845_ = l_Lean_stringToMessageData(v___x_3844_);
    return v___x_3845_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_3848_ = l_Lean_stringToMessageData(v___x_3847_);
    return v___x_3848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_3851_ = l_Lean_stringToMessageData(v___x_3850_);
    return v___x_3851_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_3854_ = l_Lean_stringToMessageData(v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_3857_ = l_Lean_stringToMessageData(v___x_3856_);
    return v___x_3857_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_3860_ = l_Lean_stringToMessageData(v___x_3859_);
    return v___x_3860_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3862_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_3863_ = l_Lean_stringToMessageData(v___x_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_msg_3864_: *mut leanh::LeanObject,
    mut v_declHint_3865_: *mut leanh::LeanObject,
    mut v___y_3866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    let mut v_isExporting_3871_: u8 = 0;
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3868_ = lean_st_ref_get(v___y_3866_);
                v_env_3869_ = leanh::lean_ctor_get(v___x_3868_, 0);
                leanh::lean_inc_ref(v_env_3869_);
                leanh::lean_dec(v___x_3868_);
                v___x_3870_ = l_Lean_Name_isAnonymous(v_declHint_3865_);
                if v___x_3870_ == 0 {
                    v_isExporting_3871_ = leanh::lean_ctor_get_uint8(
                        v_env_3869_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3871_ == 0 {
                        leanh::lean_dec_ref(v_env_3869_);
                        leanh::lean_dec(v_declHint_3865_);
                        v___x_3872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3872_, 0, v_msg_3864_);
                        return v___x_3872_;
                    } else {
                        leanh::lean_inc_ref(v_env_3869_);
                        v___x_3873_ = l_Lean_Environment_setExporting(v_env_3869_, v___x_3870_);
                        leanh::lean_inc(v_declHint_3865_);
                        leanh::lean_inc_ref(v___x_3873_);
                        v___x_3874_ = l_Lean_Environment_contains(
                            v___x_3873_,
                            v_declHint_3865_,
                            v_isExporting_3871_,
                        );
                        if v___x_3874_ == 0 {
                            leanh::lean_dec_ref(v___x_3873_);
                            leanh::lean_dec_ref(v_env_3869_);
                            leanh::lean_dec(v_declHint_3865_);
                            v___x_3875_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3875_, 0, v_msg_3864_);
                            return v___x_3875_;
                        } else {
                            v___x_3876_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_3877_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_3878_ = l_Lean_Options_empty;
                            v___x_3879_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3879_, 0, v___x_3873_);
                            leanh::lean_ctor_set(v___x_3879_, 1, v___x_3876_);
                            leanh::lean_ctor_set(v___x_3879_, 2, v___x_3877_);
                            leanh::lean_ctor_set(v___x_3879_, 3, v___x_3878_);
                            leanh::lean_inc(v_declHint_3865_);
                            v___x_3880_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3865_, v___x_3870_);
                            v_c_3881_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3881_, 0, v___x_3879_);
                            leanh::lean_ctor_set(v_c_3881_, 1, v___x_3880_);
                            v___x_3882_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3869_,
                                v_declHint_3865_,
                            );
                            if leanh::lean_obj_tag(v___x_3882_) == 0 {
                                leanh::lean_dec_ref(v_env_3869_);
                                leanh::lean_dec(v_declHint_3865_);
                                v___x_3883_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_3884_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3884_, 0, v___x_3883_);
                                leanh::lean_ctor_set(v___x_3884_, 1, v_c_3881_);
                                v___x_3885_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_3886_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3886_, 0, v___x_3884_);
                                leanh::lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                                v___x_3887_ = l_Lean_MessageData_note(v___x_3886_);
                                v___x_3888_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3888_, 0, v_msg_3864_);
                                leanh::lean_ctor_set(v___x_3888_, 1, v___x_3887_);
                                v___x_3889_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3889_, 0, v___x_3888_);
                                return v___x_3889_;
                            } else {
                                v_val_3890_ = leanh::lean_ctor_get(v___x_3882_, 0);
                                v_isSharedCheck_3925_ =
                                    (!leanh::lean_is_exclusive(v___x_3882_)) as u8;
                                if v_isSharedCheck_3925_ == 0 {
                                    v___x_3892_ = v___x_3882_;
                                    v_isShared_3893_ = v_isSharedCheck_3925_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3890_);
                                    leanh::lean_dec(v___x_3882_);
                                    v___x_3892_ = leanh::lean_box(0);
                                    v_isShared_3893_ = v_isSharedCheck_3925_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3869_);
                    leanh::lean_dec(v_declHint_3865_);
                    v___x_3926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3926_, 0, v_msg_3864_);
                    return v___x_3926_;
                }
            }
            1 => {
                v___x_3894_ = leanh::lean_box(0);
                v___x_3895_ = l_Lean_Environment_header(v_env_3869_);
                leanh::lean_dec_ref(v_env_3869_);
                v___x_3896_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3895_);
                v_mod_3897_ = lean_array_get(v___x_3894_, v___x_3896_, v_val_3890_);
                leanh::lean_dec(v_val_3890_);
                leanh::lean_dec_ref(v___x_3896_);
                v___x_3898_ = l_Lean_isPrivateName(v_declHint_3865_);
                leanh::lean_dec(v_declHint_3865_);
                if v___x_3898_ == 0 {
                    v___x_3899_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_3900_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                    leanh::lean_ctor_set(v___x_3900_, 1, v_c_3881_);
                    v___x_3901_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_3902_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3902_, 0, v___x_3900_);
                    leanh::lean_ctor_set(v___x_3902_, 1, v___x_3901_);
                    v___x_3903_ = l_Lean_MessageData_ofName(v_mod_3897_);
                    v___x_3904_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3904_, 0, v___x_3902_);
                    leanh::lean_ctor_set(v___x_3904_, 1, v___x_3903_);
                    v___x_3905_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_3906_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3906_, 0, v___x_3904_);
                    leanh::lean_ctor_set(v___x_3906_, 1, v___x_3905_);
                    v___x_3907_ = l_Lean_MessageData_note(v___x_3906_);
                    v___x_3908_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3908_, 0, v_msg_3864_);
                    leanh::lean_ctor_set(v___x_3908_, 1, v___x_3907_);
                    if v_isShared_3893_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3892_, 0);
                        leanh::lean_ctor_set(v___x_3892_, 0, v___x_3908_);
                        v___x_3910_ = v___x_3892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
                        v___x_3910_ = v_reuseFailAlloc_3911_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_3913_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3913_, 0, v___x_3912_);
                    leanh::lean_ctor_set(v___x_3913_, 1, v_c_3881_);
                    v___x_3914_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_3915_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3915_, 0, v___x_3913_);
                    leanh::lean_ctor_set(v___x_3915_, 1, v___x_3914_);
                    v___x_3916_ = l_Lean_MessageData_ofName(v_mod_3897_);
                    v___x_3917_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3917_, 0, v___x_3915_);
                    leanh::lean_ctor_set(v___x_3917_, 1, v___x_3916_);
                    v___x_3918_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_3919_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3919_, 0, v___x_3917_);
                    leanh::lean_ctor_set(v___x_3919_, 1, v___x_3918_);
                    v___x_3920_ = l_Lean_MessageData_note(v___x_3919_);
                    v___x_3921_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3921_, 0, v_msg_3864_);
                    leanh::lean_ctor_set(v___x_3921_, 1, v___x_3920_);
                    if v_isShared_3893_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3892_, 0);
                        leanh::lean_ctor_set(v___x_3892_, 0, v___x_3921_);
                        v___x_3923_ = v___x_3892_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
                        v___x_3923_ = v_reuseFailAlloc_3924_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3910_;
            }
            3 => {
                return v___x_3923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_3927_: *mut leanh::LeanObject,
    mut v_declHint_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3927_, v_declHint_3928_, v___y_3929_);
    leanh::lean_dec(v___y_3929_);
    return v_res_3931_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(
    mut v_msg_3932_: *mut leanh::LeanObject,
    mut v_declHint_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3932_, v_declHint_3933_, v___y_3937_);
                v_a_3940_ = leanh::lean_ctor_get(v___x_3939_, 0);
                v_isSharedCheck_3949_ = (!leanh::lean_is_exclusive(v___x_3939_)) as u8;
                if v_isSharedCheck_3949_ == 0 {
                    v___x_3942_ = v___x_3939_;
                    v_isShared_3943_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3940_);
                    leanh::lean_dec(v___x_3939_);
                    v___x_3942_ = leanh::lean_box(0);
                    v_isShared_3943_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3944_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3945_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3945_, 0, v___x_3944_);
                leanh::lean_ctor_set(v___x_3945_, 1, v_a_3940_);
                if v_isShared_3943_ == 0 {
                    leanh::lean_ctor_set(v___x_3942_, 0, v___x_3945_);
                    v___x_3947_ = v___x_3942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
                    v___x_3947_ = v_reuseFailAlloc_3948_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(
    mut v_msg_3950_: *mut leanh::LeanObject,
    mut v_declHint_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3950_, v_declHint_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    leanh::lean_dec(v___y_3955_);
    leanh::lean_dec_ref(v___y_3954_);
    leanh::lean_dec(v___y_3953_);
    leanh::lean_dec_ref(v___y_3952_);
    return v_res_3957_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_3958_: *mut leanh::LeanObject,
    mut v_msg_3959_: *mut leanh::LeanObject,
    mut v_declHint_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3959_, v_declHint_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
    v_a_3967_ = leanh::lean_ctor_get(v___x_3966_, 0);
    leanh::lean_inc(v_a_3967_);
    leanh::lean_dec_ref(v___x_3966_);
    v___x_3968_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3958_, v_a_3967_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
    return v___x_3968_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_3969_: *mut leanh::LeanObject,
    mut v_msg_3970_: *mut leanh::LeanObject,
    mut v_declHint_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3969_, v_msg_3970_, v_declHint_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
    leanh::lean_dec(v___y_3975_);
    leanh::lean_dec_ref(v___y_3974_);
    leanh::lean_dec(v___y_3973_);
    leanh::lean_dec_ref(v___y_3972_);
    leanh::lean_dec(v_ref_3969_);
    return v_res_3977_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3979_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3980_ = l_Lean_stringToMessageData(v___x_3979_);
    return v___x_3980_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3982_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3983_ = l_Lean_stringToMessageData(v___x_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3984_: *mut leanh::LeanObject,
    mut v_constName_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3991_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3992_ = 0;
    leanh::lean_inc(v_constName_3985_);
    v___x_3993_ = l_Lean_MessageData_ofConstName(v_constName_3985_, v___x_3992_);
    v___x_3994_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3994_, 0, v___x_3991_);
    leanh::lean_ctor_set(v___x_3994_, 1, v___x_3993_);
    v___x_3995_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3996_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3996_, 0, v___x_3994_);
    leanh::lean_ctor_set(v___x_3996_, 1, v___x_3995_);
    v___x_3997_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3984_, v___x_3996_, v_constName_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
    return v___x_3997_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3998_: *mut leanh::LeanObject,
    mut v_constName_3999_: *mut leanh::LeanObject,
    mut v___y_4000_: *mut leanh::LeanObject,
    mut v___y_4001_: *mut leanh::LeanObject,
    mut v___y_4002_: *mut leanh::LeanObject,
    mut v___y_4003_: *mut leanh::LeanObject,
    mut v___y_4004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_3998_, v_constName_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
    leanh::lean_dec(v___y_4003_);
    leanh::lean_dec_ref(v___y_4002_);
    leanh::lean_dec(v___y_4001_);
    leanh::lean_dec_ref(v___y_4000_);
    leanh::lean_dec(v_ref_3998_);
    return v_res_4005_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(
    mut v_constName_4006_: *mut leanh::LeanObject,
    mut v___y_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
    mut v___y_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4012_ = leanh::lean_ctor_get(v___y_4009_, 5);
    v___x_4013_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_4012_, v_constName_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
    return v___x_4013_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg___boxed(
    mut v_constName_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
    mut v___y_4016_: *mut leanh::LeanObject,
    mut v___y_4017_: *mut leanh::LeanObject,
    mut v___y_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4020_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
    leanh::lean_dec(v___y_4018_);
    leanh::lean_dec_ref(v___y_4017_);
    leanh::lean_dec(v___y_4016_);
    leanh::lean_dec_ref(v___y_4015_);
    return v_res_4020_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(
    mut v_constName_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
    mut v___y_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4027_ = lean_st_ref_get(v___y_4025_);
                v_env_4028_ = leanh::lean_ctor_get(v___x_4027_, 0);
                leanh::lean_inc_ref(v_env_4028_);
                leanh::lean_dec(v___x_4027_);
                v___x_4029_ = 0;
                leanh::lean_inc(v_constName_4021_);
                v___x_4030_ =
                    l_Lean_Environment_find_x3f(v_env_4028_, v_constName_4021_, v___x_4029_);
                if leanh::lean_obj_tag(v___x_4030_) == 0 {
                    v___x_4031_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
                    return v___x_4031_;
                } else {
                    leanh::lean_dec(v_constName_4021_);
                    v_val_4032_ = leanh::lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4039_ = (!leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4039_ == 0 {
                        v___x_4034_ = v___x_4030_;
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4032_);
                        leanh::lean_dec(v___x_4030_);
                        v___x_4034_ = leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4035_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4034_, 0);
                    v___x_4037_ = v___x_4034_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_val_4032_);
                    v___x_4037_ = v_reuseFailAlloc_4038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0___boxed(
    mut v_constName_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
    mut v___y_4042_: *mut leanh::LeanObject,
    mut v___y_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ =
        l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(
            v_constName_4040_,
            v___y_4041_,
            v___y_4042_,
            v___y_4043_,
            v___y_4044_,
        );
    leanh::lean_dec(v___y_4044_);
    leanh::lean_dec_ref(v___y_4043_);
    leanh::lean_dec(v___y_4042_);
    leanh::lean_dec_ref(v___y_4041_);
    return v_res_4046_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(
    mut v_x_4047_: *mut leanh::LeanObject,
    mut v_a_4048_: *mut leanh::LeanObject,
    mut v_a_4049_: *mut leanh::LeanObject,
    mut v_a_4050_: *mut leanh::LeanObject,
    mut v_a_4051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4058_: u8 = 0;
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_a_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_fvarId_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_proof_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4047_) {
                0 => {
                    v_declName_4053_ = leanh::lean_ctor_get(v_x_4047_, 0);
                    leanh::lean_inc_n(v_declName_4053_, 2);
                    leanh::lean_dec_ref_known(v_x_4047_, 1);
                    v___x_4054_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_4053_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
                    if leanh::lean_obj_tag(v___x_4054_) == 0 {
                        v_a_4055_ = leanh::lean_ctor_get(v___x_4054_, 0);
                        v_isSharedCheck_4067_ =
                            (!leanh::lean_is_exclusive(v___x_4054_)) as u8;
                        if v_isSharedCheck_4067_ == 0 {
                            v___x_4057_ = v___x_4054_;
                            v_isShared_4058_ = v_isSharedCheck_4067_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4055_);
                            leanh::lean_dec(v___x_4054_);
                            v___x_4057_ = leanh::lean_box(0);
                            v_isShared_4058_ = v_isSharedCheck_4067_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_4053_);
                        v_a_4068_ = leanh::lean_ctor_get(v___x_4054_, 0);
                        v_isSharedCheck_4075_ =
                            (!leanh::lean_is_exclusive(v___x_4054_)) as u8;
                        if v_isSharedCheck_4075_ == 0 {
                            v___x_4070_ = v___x_4054_;
                            v_isShared_4071_ = v_isSharedCheck_4075_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4068_);
                            leanh::lean_dec(v___x_4054_);
                            v___x_4070_ = leanh::lean_box(0);
                            v_isShared_4071_ = v_isSharedCheck_4075_;
                            state = 3;
                            continue;
                        }
                    }
                }
                1 => {
                    v_fvarId_4076_ = leanh::lean_ctor_get(v_x_4047_, 0);
                    v_isSharedCheck_4086_ = (!leanh::lean_is_exclusive(v_x_4047_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v___x_4078_ = v_x_4047_;
                        v_isShared_4079_ = v_isSharedCheck_4086_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_4076_);
                        leanh::lean_dec(v_x_4047_);
                        v___x_4078_ = leanh::lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4086_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_proof_4087_ = leanh::lean_ctor_get(v_x_4047_, 2);
                    leanh::lean_inc_ref(v_proof_4087_);
                    leanh::lean_dec_ref_known(v_x_4047_, 3);
                    v___x_4088_ = leanh::lean_box(0);
                    v___x_4089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4089_, 0, v___x_4088_);
                    leanh::lean_ctor_set(v___x_4089_, 1, v_proof_4087_);
                    v___x_4090_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4090_, 0, v___x_4089_);
                    return v___x_4090_;
                }
            },
            1 => {
                v___x_4059_ = l_Lean_ConstantInfo_levelParams(v_a_4055_);
                leanh::lean_dec(v_a_4055_);
                v___x_4060_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_4059_);
                v___x_4061_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_4059_, v___x_4060_);
                v___x_4062_ = l_Lean_mkConst(v_declName_4053_, v___x_4061_);
                v___x_4063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4063_, 0, v___x_4059_);
                leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                if v_isShared_4058_ == 0 {
                    leanh::lean_ctor_set(v___x_4057_, 0, v___x_4063_);
                    v___x_4065_ = v___x_4057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
                    v___x_4065_ = v_reuseFailAlloc_4066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4065_;
            }
            3 => {
                if v_isShared_4071_ == 0 {
                    v___x_4073_ = v___x_4070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
                    v___x_4073_ = v_reuseFailAlloc_4074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4073_;
            }
            5 => {
                v___x_4080_ = leanh::lean_box(0);
                v___x_4081_ = l_Lean_mkFVar(v_fvarId_4076_);
                v___x_4082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4082_, 0, v___x_4080_);
                leanh::lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                if v_isShared_4079_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4078_, 0);
                    leanh::lean_ctor_set(v___x_4078_, 0, v___x_4082_);
                    v___x_4084_ = v___x_4078_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
                    v___x_4084_ = v_reuseFailAlloc_4085_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof___boxed(
    mut v_x_4091_: *mut leanh::LeanObject,
    mut v_a_4092_: *mut leanh::LeanObject,
    mut v_a_4093_: *mut leanh::LeanObject,
    mut v_a_4094_: *mut leanh::LeanObject,
    mut v_a_4095_: *mut leanh::LeanObject,
    mut v_a_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(
        v_x_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_,
    );
    leanh::lean_dec(v_a_4095_);
    leanh::lean_dec_ref(v_a_4094_);
    leanh::lean_dec(v_a_4093_);
    leanh::lean_dec_ref(v_a_4092_);
    return v_res_4097_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(
    mut v_00_u03b1_4098_: *mut leanh::LeanObject,
    mut v_constName_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
    mut v___y_4101_: *mut leanh::LeanObject,
    mut v___y_4102_: *mut leanh::LeanObject,
    mut v___y_4103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
    return v___x_4105_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___boxed(
    mut v_00_u03b1_4106_: *mut leanh::LeanObject,
    mut v_constName_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4113_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(v_00_u03b1_4106_, v_constName_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
    leanh::lean_dec(v___y_4111_);
    leanh::lean_dec_ref(v___y_4110_);
    leanh::lean_dec(v___y_4109_);
    leanh::lean_dec_ref(v___y_4108_);
    return v_res_4113_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4114_: *mut leanh::LeanObject,
    mut v_ref_4115_: *mut leanh::LeanObject,
    mut v_constName_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_4115_, v_constName_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4123_: *mut leanh::LeanObject,
    mut v_ref_4124_: *mut leanh::LeanObject,
    mut v_constName_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4131_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(v_00_u03b1_4123_, v_ref_4124_, v_constName_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
    leanh::lean_dec(v___y_4129_);
    leanh::lean_dec_ref(v___y_4128_);
    leanh::lean_dec(v___y_4127_);
    leanh::lean_dec_ref(v___y_4126_);
    leanh::lean_dec(v_ref_4124_);
    return v_res_4131_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_4132_: *mut leanh::LeanObject,
    mut v_ref_4133_: *mut leanh::LeanObject,
    mut v_msg_4134_: *mut leanh::LeanObject,
    mut v_declHint_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
    mut v___y_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4141_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4133_, v_msg_4134_, v_declHint_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
    return v___x_4141_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_4142_: *mut leanh::LeanObject,
    mut v_ref_4143_: *mut leanh::LeanObject,
    mut v_msg_4144_: *mut leanh::LeanObject,
    mut v_declHint_4145_: *mut leanh::LeanObject,
    mut v___y_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
    mut v___y_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4151_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4142_, v_ref_4143_, v_msg_4144_, v_declHint_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
    leanh::lean_dec(v___y_4149_);
    leanh::lean_dec_ref(v___y_4148_);
    leanh::lean_dec(v___y_4147_);
    leanh::lean_dec_ref(v___y_4146_);
    leanh::lean_dec(v_ref_4143_);
    return v_res_4151_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(
    mut v_msg_4152_: *mut leanh::LeanObject,
    mut v_declHint_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4152_, v_declHint_4153_, v___y_4157_);
    return v___x_4159_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(
    mut v_msg_4160_: *mut leanh::LeanObject,
    mut v_declHint_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
    mut v___y_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4167_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_4160_, v_declHint_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
    leanh::lean_dec(v___y_4165_);
    leanh::lean_dec_ref(v___y_4164_);
    leanh::lean_dec(v___y_4163_);
    leanh::lean_dec_ref(v___y_4162_);
    return v_res_4167_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b1_4168_: *mut leanh::LeanObject,
    mut v_ref_4169_: *mut leanh::LeanObject,
    mut v_msg_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
    mut v___y_4172_: *mut leanh::LeanObject,
    mut v___y_4173_: *mut leanh::LeanObject,
    mut v___y_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4169_, v_msg_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
    return v___x_4176_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b1_4177_: *mut leanh::LeanObject,
    mut v_ref_4178_: *mut leanh::LeanObject,
    mut v_msg_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
    mut v___y_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4177_, v_ref_4178_, v_msg_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
    leanh::lean_dec(v___y_4183_);
    leanh::lean_dec_ref(v___y_4182_);
    leanh::lean_dec(v___y_4181_);
    leanh::lean_dec_ref(v___y_4180_);
    leanh::lean_dec(v_ref_4178_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(
    mut v_00_u03b1_4186_: *mut leanh::LeanObject,
    mut v_msg_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_4194_: *mut leanh::LeanObject,
    mut v_msg_4195_: *mut leanh::LeanObject,
    mut v___y_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4201_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_4194_, v_msg_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
    leanh::lean_dec(v___y_4199_);
    leanh::lean_dec_ref(v___y_4198_);
    leanh::lean_dec(v___y_4197_);
    leanh::lean_dec_ref(v___y_4196_);
    return v_res_4201_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0()
-> u64 {
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u64 = 0;
    v___x_4202_ = leanh::lean_unsigned_to_nat(1723);
    v___x_4203_ = lean_uint64_of_nat(v___x_4202_);
    return v___x_4203_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(
    mut v_sp_4204_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___y_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: u64 = 0;
    let mut v_hash_4208_: u64 = 0;
    let mut v_declName_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_4209_ = leanh::lean_ctor_get(v_sp_4204_, 0);
                v___y_4206_ = v_declName_4209_;
                state = 1;
                continue;
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4206_) == 0 {
                    v___x_4207_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    return v___x_4207_;
                } else {
                    v_hash_4208_ = leanh::lean_ctor_get_uint64(
                        v___y_4206_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    return v_hash_4208_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed(
    mut v_sp_4210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4211_: u64 = 0;
    let mut v_r_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(v_sp_4210_);
    leanh::lean_dec_ref(v_sp_4210_);
    v_r_4212_ = leanh::lean_box_uint64(v_res_4211_);
    return v_r_4212_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(
    mut v_e_4215_: *mut leanh::LeanObject,
    mut v___y_4216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4218_: u8 = 0;
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_unused_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4218_ = l_Lean_Expr_hasMVar(v_e_4215_);
                if v___x_4218_ == 0 {
                    v___x_4219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4219_, 0, v_e_4215_);
                    return v___x_4219_;
                } else {
                    v___x_4220_ = lean_st_ref_get(v___y_4216_);
                    v_mctx_4221_ = leanh::lean_ctor_get(v___x_4220_, 0);
                    leanh::lean_inc_ref(v_mctx_4221_);
                    leanh::lean_dec(v___x_4220_);
                    v___x_4222_ = l_Lean_instantiateMVarsCore(v_mctx_4221_, v_e_4215_);
                    v_fst_4223_ = leanh::lean_ctor_get(v___x_4222_, 0);
                    leanh::lean_inc(v_fst_4223_);
                    v_snd_4224_ = leanh::lean_ctor_get(v___x_4222_, 1);
                    leanh::lean_inc(v_snd_4224_);
                    leanh::lean_dec_ref(v___x_4222_);
                    v___x_4225_ = lean_st_ref_take(v___y_4216_);
                    v_cache_4226_ = leanh::lean_ctor_get(v___x_4225_, 1);
                    v_zetaDeltaFVarIds_4227_ = leanh::lean_ctor_get(v___x_4225_, 2);
                    v_postponed_4228_ = leanh::lean_ctor_get(v___x_4225_, 3);
                    v_diag_4229_ = leanh::lean_ctor_get(v___x_4225_, 4);
                    v_isSharedCheck_4238_ = (!leanh::lean_is_exclusive(v___x_4225_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v_unused_4239_ = leanh::lean_ctor_get(v___x_4225_, 0);
                        leanh::lean_dec(v_unused_4239_);
                        v___x_4231_ = v___x_4225_;
                        v_isShared_4232_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_4229_);
                        leanh::lean_inc(v_postponed_4228_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_4227_);
                        leanh::lean_inc(v_cache_4226_);
                        leanh::lean_dec(v___x_4225_);
                        v___x_4231_ = leanh::lean_box(0);
                        v_isShared_4232_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4232_ == 0 {
                    leanh::lean_ctor_set(v___x_4231_, 0, v_snd_4224_);
                    v___x_4234_ = v___x_4231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_snd_4224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_cache_4226_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4237_,
                        2,
                        v_zetaDeltaFVarIds_4227_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_postponed_4228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_diag_4229_);
                    v___x_4234_ = v_reuseFailAlloc_4237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4235_ = lean_st_ref_set(v___y_4216_, v___x_4234_);
                v___x_4236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4236_, 0, v_fst_4223_);
                return v___x_4236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg___boxed(
    mut v_e_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4243_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_4240_, v___y_4241_);
    leanh::lean_dec(v___y_4241_);
    return v_res_4243_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(
    mut v_e_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
    mut v___y_4246_: *mut leanh::LeanObject,
    mut v___y_4247_: *mut leanh::LeanObject,
    mut v___y_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_4244_, v___y_4246_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___boxed(
    mut v_e_4251_: *mut leanh::LeanObject,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4257_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(
            v_e_4251_,
            v___y_4252_,
            v___y_4253_,
            v___y_4254_,
            v___y_4255_,
        );
    leanh::lean_dec(v___y_4255_);
    leanh::lean_dec_ref(v___y_4254_);
    leanh::lean_dec(v___y_4253_);
    leanh::lean_dec_ref(v___y_4252_);
    return v_res_4257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(
    mut v_proof_4258_: *mut leanh::LeanObject,
    mut v_a_4259_: *mut leanh::LeanObject,
    mut v_a_4260_: *mut leanh::LeanObject,
    mut v_a_4261_: *mut leanh::LeanObject,
    mut v_a_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_prf_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v_snd_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v_fst_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4289_: u8 = 0;
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut v_a_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v_a_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v_declName_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4330_: u8 = 0;
    let mut v_fvarId_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_proof_4258_) {
                0 => {
                    v_declName_4320_ = leanh::lean_ctor_get(v_proof_4258_, 0);
                    leanh::lean_inc(v_declName_4320_);
                    leanh::lean_dec_ref_known(v_proof_4258_, 1);
                    v___x_4321_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                        v_declName_4320_,
                        v_a_4259_,
                        v_a_4260_,
                        v_a_4261_,
                        v_a_4262_,
                    );
                    if leanh::lean_obj_tag(v___x_4321_) == 0 {
                        v_a_4322_ = leanh::lean_ctor_get(v___x_4321_, 0);
                        leanh::lean_inc(v_a_4322_);
                        leanh::lean_dec_ref_known(v___x_4321_, 1);
                        v_prf_4265_ = v_a_4322_;
                        v___y_4266_ = v_a_4259_;
                        v___y_4267_ = v_a_4260_;
                        v___y_4268_ = v_a_4261_;
                        v___y_4269_ = v_a_4262_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4323_ = leanh::lean_ctor_get(v___x_4321_, 0);
                        v_isSharedCheck_4330_ =
                            (!leanh::lean_is_exclusive(v___x_4321_)) as u8;
                        if v_isSharedCheck_4330_ == 0 {
                            v___x_4325_ = v___x_4321_;
                            v_isShared_4326_ = v_isSharedCheck_4330_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4323_);
                            leanh::lean_dec(v___x_4321_);
                            v___x_4325_ = leanh::lean_box(0);
                            v_isShared_4326_ = v_isSharedCheck_4330_;
                            state = 12;
                            continue;
                        }
                    }
                }
                1 => {
                    v_fvarId_4331_ = leanh::lean_ctor_get(v_proof_4258_, 0);
                    leanh::lean_inc(v_fvarId_4331_);
                    leanh::lean_dec_ref_known(v_proof_4258_, 1);
                    v___x_4332_ = l_Lean_mkFVar(v_fvarId_4331_);
                    v_prf_4265_ = v___x_4332_;
                    v___y_4266_ = v_a_4259_;
                    v___y_4267_ = v_a_4260_;
                    v___y_4268_ = v_a_4261_;
                    v___y_4269_ = v_a_4262_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_proof_4333_ = leanh::lean_ctor_get(v_proof_4258_, 2);
                    leanh::lean_inc_ref(v_proof_4333_);
                    leanh::lean_dec_ref_known(v_proof_4258_, 3);
                    v_prf_4265_ = v_proof_4333_;
                    v___y_4266_ = v_a_4259_;
                    v___y_4267_ = v_a_4260_;
                    v___y_4268_ = v_a_4261_;
                    v___y_4269_ = v_a_4262_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                leanh::lean_inc(v___y_4269_);
                leanh::lean_inc_ref(v___y_4268_);
                leanh::lean_inc(v___y_4267_);
                leanh::lean_inc_ref(v___y_4266_);
                leanh::lean_inc_ref(v_prf_4265_);
                v___x_4270_ = lean_infer_type(
                    v_prf_4265_,
                    v___y_4266_,
                    v___y_4267_,
                    v___y_4268_,
                    v___y_4269_,
                );
                if leanh::lean_obj_tag(v___x_4270_) == 0 {
                    v_a_4271_ = leanh::lean_ctor_get(v___x_4270_, 0);
                    leanh::lean_inc(v_a_4271_);
                    leanh::lean_dec_ref_known(v___x_4270_, 1);
                    v___x_4272_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_a_4271_, v___y_4267_);
                    v_a_4273_ = leanh::lean_ctor_get(v___x_4272_, 0);
                    leanh::lean_inc(v_a_4273_);
                    leanh::lean_dec_ref(v___x_4272_);
                    v___x_4274_ = 0;
                    v___x_4275_ = l_Lean_Meta_forallMetaTelescope(
                        v_a_4273_,
                        v___x_4274_,
                        v___y_4266_,
                        v___y_4267_,
                        v___y_4268_,
                        v___y_4269_,
                    );
                    if leanh::lean_obj_tag(v___x_4275_) == 0 {
                        v_a_4276_ = leanh::lean_ctor_get(v___x_4275_, 0);
                        v_isSharedCheck_4303_ =
                            (!leanh::lean_is_exclusive(v___x_4275_)) as u8;
                        if v_isSharedCheck_4303_ == 0 {
                            v___x_4278_ = v___x_4275_;
                            v_isShared_4279_ = v_isSharedCheck_4303_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4276_);
                            leanh::lean_dec(v___x_4275_);
                            v___x_4278_ = leanh::lean_box(0);
                            v_isShared_4279_ = v_isSharedCheck_4303_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prf_4265_);
                        v_a_4304_ = leanh::lean_ctor_get(v___x_4275_, 0);
                        v_isSharedCheck_4311_ =
                            (!leanh::lean_is_exclusive(v___x_4275_)) as u8;
                        if v_isSharedCheck_4311_ == 0 {
                            v___x_4306_ = v___x_4275_;
                            v_isShared_4307_ = v_isSharedCheck_4311_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4304_);
                            leanh::lean_dec(v___x_4275_);
                            v___x_4306_ = leanh::lean_box(0);
                            v_isShared_4307_ = v_isSharedCheck_4311_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_prf_4265_);
                    v_a_4312_ = leanh::lean_ctor_get(v___x_4270_, 0);
                    v_isSharedCheck_4319_ = (!leanh::lean_is_exclusive(v___x_4270_)) as u8;
                    if v_isSharedCheck_4319_ == 0 {
                        v___x_4314_ = v___x_4270_;
                        v_isShared_4315_ = v_isSharedCheck_4319_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4312_);
                        leanh::lean_dec(v___x_4270_);
                        v___x_4314_ = leanh::lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4319_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_4280_ = leanh::lean_ctor_get(v_a_4276_, 1);
                v_fst_4281_ = leanh::lean_ctor_get(v_a_4276_, 0);
                v_isSharedCheck_4302_ = (!leanh::lean_is_exclusive(v_a_4276_)) as u8;
                if v_isSharedCheck_4302_ == 0 {
                    v___x_4283_ = v_a_4276_;
                    v_isShared_4284_ = v_isSharedCheck_4302_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4280_);
                    leanh::lean_inc(v_fst_4281_);
                    leanh::lean_dec(v_a_4276_);
                    v___x_4283_ = leanh::lean_box(0);
                    v_isShared_4284_ = v_isSharedCheck_4302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4285_ = leanh::lean_ctor_get(v_snd_4280_, 0);
                v_snd_4286_ = leanh::lean_ctor_get(v_snd_4280_, 1);
                v_isSharedCheck_4301_ = (!leanh::lean_is_exclusive(v_snd_4280_)) as u8;
                if v_isSharedCheck_4301_ == 0 {
                    v___x_4288_ = v_snd_4280_;
                    v_isShared_4289_ = v_isSharedCheck_4301_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4286_);
                    leanh::lean_inc(v_fst_4285_);
                    leanh::lean_dec(v_snd_4280_);
                    v___x_4288_ = leanh::lean_box(0);
                    v_isShared_4289_ = v_isSharedCheck_4301_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_fst_4281_);
                v___x_4290_ = l_Lean_Expr_beta(v_prf_4265_, v_fst_4281_);
                if v_isShared_4289_ == 0 {
                    leanh::lean_ctor_set(v___x_4288_, 0, v___x_4290_);
                    v___x_4292_ = v___x_4288_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 1, v_snd_4286_);
                    v___x_4292_ = v_reuseFailAlloc_4300_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4284_ == 0 {
                    leanh::lean_ctor_set(v___x_4283_, 1, v___x_4292_);
                    leanh::lean_ctor_set(v___x_4283_, 0, v_fst_4285_);
                    v___x_4294_ = v___x_4283_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4299_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_fst_4285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 1, v___x_4292_);
                    v___x_4294_ = v_reuseFailAlloc_4299_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4295_, 0, v_fst_4281_);
                leanh::lean_ctor_set(v___x_4295_, 1, v___x_4294_);
                if v_isShared_4279_ == 0 {
                    leanh::lean_ctor_set(v___x_4278_, 0, v___x_4295_);
                    v___x_4297_ = v___x_4278_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4297_;
            }
            8 => {
                if v_isShared_4307_ == 0 {
                    v___x_4309_ = v___x_4306_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
                    v___x_4309_ = v_reuseFailAlloc_4310_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4309_;
            }
            10 => {
                if v_isShared_4315_ == 0 {
                    v___x_4317_ = v___x_4314_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
                    v___x_4317_ = v_reuseFailAlloc_4318_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4317_;
            }
            12 => {
                if v_isShared_4326_ == 0 {
                    v___x_4328_ = v___x_4325_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4329_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
                    v___x_4328_ = v_reuseFailAlloc_4329_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate___boxed(
    mut v_proof_4334_: *mut leanh::LeanObject,
    mut v_a_4335_: *mut leanh::LeanObject,
    mut v_a_4336_: *mut leanh::LeanObject,
    mut v_a_4337_: *mut leanh::LeanObject,
    mut v_a_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(
        v_proof_4334_,
        v_a_4335_,
        v_a_4336_,
        v_a_4337_,
        v_a_4338_,
    );
    leanh::lean_dec(v_a_4338_);
    leanh::lean_dec_ref(v_a_4337_);
    leanh::lean_dec(v_a_4336_);
    leanh::lean_dec_ref(v_a_4335_);
    return v_res_4340_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0;
    v___x_4343_ = l_Lean_stringToMessageData(v___x_4342_);
    return v___x_4343_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2;
    v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4;
    v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
    return v___x_4349_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4351_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6;
    v___x_4352_ = l_Lean_stringToMessageData(v___x_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0(
    mut v_x_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4353_) {
        0 => {
            let mut v_declName_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_4354_ = leanh::lean_ctor_get(v_x_4353_, 0);
            leanh::lean_inc(v_declName_4354_);
            leanh::lean_dec_ref_known(v_x_4353_, 1);
            v___x_4355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1);
            v___x_4356_ = l_Lean_MessageData_ofName(v_declName_4354_);
            v___x_4357_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4357_, 0, v___x_4355_);
            leanh::lean_ctor_set(v___x_4357_, 1, v___x_4356_);
            return v___x_4357_;
        }
        1 => {
            let mut v_fvarId_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_4358_ = leanh::lean_ctor_get(v_x_4353_, 0);
            leanh::lean_inc(v_fvarId_4358_);
            leanh::lean_dec_ref_known(v_x_4353_, 1);
            v___x_4359_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3);
            v___x_4360_ = l_Lean_mkFVar(v_fvarId_4358_);
            v___x_4361_ = l_Lean_MessageData_ofExpr(v___x_4360_);
            v___x_4362_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4362_, 0, v___x_4359_);
            leanh::lean_ctor_set(v___x_4362_, 1, v___x_4361_);
            return v___x_4362_;
        }
        _ => {
            let mut v_ref_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_proof_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_4363_ = leanh::lean_ctor_get(v_x_4353_, 1);
            leanh::lean_inc(v_ref_4363_);
            v_proof_4364_ = leanh::lean_ctor_get(v_x_4353_, 2);
            leanh::lean_inc_ref(v_proof_4364_);
            leanh::lean_dec_ref_known(v_x_4353_, 3);
            v___x_4365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5);
            v___x_4366_ = l_Lean_MessageData_ofSyntax(v_ref_4363_);
            v___x_4367_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4367_, 0, v___x_4365_);
            leanh::lean_ctor_set(v___x_4367_, 1, v___x_4366_);
            v___x_4368_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7);
            v___x_4369_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4369_, 0, v___x_4367_);
            leanh::lean_ctor_set(v___x_4369_, 1, v___x_4368_);
            v___x_4370_ = l_Lean_MessageData_ofExpr(v_proof_4364_);
            v___x_4371_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4371_, 0, v___x_4369_);
            leanh::lean_ctor_set(v___x_4371_, 1, v___x_4370_);
            return v___x_4371_;
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4379_ = leanh::lean_box(0);
    v___x_4380_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2;
    v___x_4381_ = l_Lean_Expr_const___override(v___x_4380_, v___x_4379_);
    return v___x_4381_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = leanh::lean_unsigned_to_nat(1000);
    v___x_4383_ = leanh::lean_unsigned_to_nat(0);
    v___x_4384_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default;
    v___x_4385_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3,
    );
    v___x_4386_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0;
    v___x_4387_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4387_, 0, v___x_4386_);
    leanh::lean_ctor_set(v___x_4387_, 1, v___x_4385_);
    leanh::lean_ctor_set(v___x_4387_, 2, v___x_4384_);
    leanh::lean_ctor_set(v___x_4387_, 3, v___x_4383_);
    leanh::lean_ctor_set(v___x_4387_, 4, v___x_4382_);
    return v___x_4387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default()
-> *mut leanh::LeanObject {
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4,
    );
    return v___x_4388_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem()
-> *mut leanh::LeanObject {
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default;
    return v___x_4389_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(
    mut v_xs_4390_: *mut leanh::LeanObject,
    mut v_ys_4391_: *mut leanh::LeanObject,
    mut v_x_4392_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4394_: u8 = 0;
    let mut v_one_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4393_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4394_ = lean_nat_dec_eq(v_x_4392_, v_zero_4393_);
                if v_isZero_4394_ == 1 {
                    leanh::lean_dec(v_x_4392_);
                    return v_isZero_4394_;
                } else {
                    v_one_4395_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4396_ = lean_nat_sub(v_x_4392_, v_one_4395_);
                    leanh::lean_dec(v_x_4392_);
                    v___x_4397_ = lean_array_fget_borrowed(v_xs_4390_, v_n_4396_);
                    v___x_4398_ = lean_array_fget_borrowed(v_ys_4391_, v_n_4396_);
                    v___x_4399_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_4397_, v___x_4398_);
                    if v___x_4399_ == 0 {
                        leanh::lean_dec(v_n_4396_);
                        return v___x_4399_;
                    } else {
                        v_x_4392_ = v_n_4396_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg___boxed(
    mut v_xs_4401_: *mut leanh::LeanObject,
    mut v_ys_4402_: *mut leanh::LeanObject,
    mut v_x_4403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4404_: u8 = 0;
    let mut v_r_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4404_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_4401_, v_ys_4402_, v_x_4403_);
    leanh::lean_dec_ref(v_ys_4402_);
    leanh::lean_dec_ref(v_xs_4401_);
    v_r_4405_ = leanh::lean_box((v_res_4404_) as usize);
    return v_r_4405_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(
    mut v_x_4406_: *mut leanh::LeanObject,
    mut v_x_4407_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_keys_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prog_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_etaPotential_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prog_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_etaPotential_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: u8 = 0;
    v_keys_4408_ = leanh::lean_ctor_get(v_x_4406_, 0);
    leanh::lean_inc_ref(v_keys_4408_);
    v_prog_4409_ = leanh::lean_ctor_get(v_x_4406_, 1);
    leanh::lean_inc_ref(v_prog_4409_);
    v_proof_4410_ = leanh::lean_ctor_get(v_x_4406_, 2);
    leanh::lean_inc_ref(v_proof_4410_);
    v_etaPotential_4411_ = leanh::lean_ctor_get(v_x_4406_, 3);
    leanh::lean_inc(v_etaPotential_4411_);
    v_priority_4412_ = leanh::lean_ctor_get(v_x_4406_, 4);
    leanh::lean_inc(v_priority_4412_);
    leanh::lean_dec_ref(v_x_4406_);
    v_keys_4413_ = leanh::lean_ctor_get(v_x_4407_, 0);
    leanh::lean_inc_ref(v_keys_4413_);
    v_prog_4414_ = leanh::lean_ctor_get(v_x_4407_, 1);
    leanh::lean_inc_ref(v_prog_4414_);
    v_proof_4415_ = leanh::lean_ctor_get(v_x_4407_, 2);
    leanh::lean_inc_ref(v_proof_4415_);
    v_etaPotential_4416_ = leanh::lean_ctor_get(v_x_4407_, 3);
    leanh::lean_inc(v_etaPotential_4416_);
    v_priority_4417_ = leanh::lean_ctor_get(v_x_4407_, 4);
    leanh::lean_inc(v_priority_4417_);
    leanh::lean_dec_ref(v_x_4407_);
    v___x_4418_ = lean_array_get_size(v_keys_4408_);
    v___x_4419_ = lean_array_get_size(v_keys_4413_);
    v___x_4420_ = lean_nat_dec_eq(v___x_4418_, v___x_4419_);
    if v___x_4420_ == 0 {
        leanh::lean_dec(v_priority_4417_);
        leanh::lean_dec(v_etaPotential_4416_);
        leanh::lean_dec_ref(v_proof_4415_);
        leanh::lean_dec_ref(v_prog_4414_);
        leanh::lean_dec_ref(v_keys_4413_);
        leanh::lean_dec(v_priority_4412_);
        leanh::lean_dec(v_etaPotential_4411_);
        leanh::lean_dec_ref(v_proof_4410_);
        leanh::lean_dec_ref(v_prog_4409_);
        leanh::lean_dec_ref(v_keys_4408_);
        return v___x_4420_;
    } else {
        let mut v___x_4421_: u8 = 0;
        v___x_4421_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_keys_4408_, v_keys_4413_, v___x_4418_);
        leanh::lean_dec_ref(v_keys_4413_);
        leanh::lean_dec_ref(v_keys_4408_);
        if v___x_4421_ == 0 {
            leanh::lean_dec(v_priority_4417_);
            leanh::lean_dec(v_etaPotential_4416_);
            leanh::lean_dec_ref(v_proof_4415_);
            leanh::lean_dec_ref(v_prog_4414_);
            leanh::lean_dec(v_priority_4412_);
            leanh::lean_dec(v_etaPotential_4411_);
            leanh::lean_dec_ref(v_proof_4410_);
            leanh::lean_dec_ref(v_prog_4409_);
            return v___x_4421_;
        } else {
            let mut v___x_4422_: u8 = 0;
            v___x_4422_ = lean_expr_eqv(v_prog_4409_, v_prog_4414_);
            leanh::lean_dec_ref(v_prog_4414_);
            leanh::lean_dec_ref(v_prog_4409_);
            if v___x_4422_ == 0 {
                leanh::lean_dec(v_priority_4417_);
                leanh::lean_dec(v_etaPotential_4416_);
                leanh::lean_dec_ref(v_proof_4415_);
                leanh::lean_dec(v_priority_4412_);
                leanh::lean_dec(v_etaPotential_4411_);
                leanh::lean_dec_ref(v_proof_4410_);
                return v___x_4422_;
            } else {
                let mut v___x_4423_: u8 = 0;
                v___x_4423_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                    v_proof_4410_,
                    v_proof_4415_,
                );
                if v___x_4423_ == 0 {
                    leanh::lean_dec(v_priority_4417_);
                    leanh::lean_dec(v_etaPotential_4416_);
                    leanh::lean_dec(v_priority_4412_);
                    leanh::lean_dec(v_etaPotential_4411_);
                    return v___x_4423_;
                } else {
                    let mut v___x_4424_: u8 = 0;
                    v___x_4424_ = lean_nat_dec_eq(v_etaPotential_4411_, v_etaPotential_4416_);
                    leanh::lean_dec(v_etaPotential_4416_);
                    leanh::lean_dec(v_etaPotential_4411_);
                    if v___x_4424_ == 0 {
                        leanh::lean_dec(v_priority_4417_);
                        leanh::lean_dec(v_priority_4412_);
                        return v___x_4424_;
                    } else {
                        let mut v___x_4425_: u8 = 0;
                        v___x_4425_ = lean_nat_dec_eq(v_priority_4412_, v_priority_4417_);
                        leanh::lean_dec(v_priority_4417_);
                        leanh::lean_dec(v_priority_4412_);
                        return v___x_4425_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed(
    mut v_x_4426_: *mut leanh::LeanObject,
    mut v_x_4427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4428_: u8 = 0;
    let mut v_r_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_x_4426_, v_x_4427_);
    v_r_4429_ = leanh::lean_box((v_res_4428_) as usize);
    return v_r_4429_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(
    mut v_xs_4430_: *mut leanh::LeanObject,
    mut v_ys_4431_: *mut leanh::LeanObject,
    mut v_hsz_4432_: *mut leanh::LeanObject,
    mut v_x_4433_: *mut leanh::LeanObject,
    mut v_x_4434_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4435_: u8 = 0;
    v___x_4435_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_4430_, v_ys_4431_, v_x_4433_);
    return v___x_4435_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___boxed(
    mut v_xs_4436_: *mut leanh::LeanObject,
    mut v_ys_4437_: *mut leanh::LeanObject,
    mut v_hsz_4438_: *mut leanh::LeanObject,
    mut v_x_4439_: *mut leanh::LeanObject,
    mut v_x_4440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4441_: u8 = 0;
    let mut v_r_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4441_ =
        l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(
            v_xs_4436_,
            v_ys_4437_,
            v_hsz_4438_,
            v_x_4439_,
            v_x_4440_,
        );
    leanh::lean_dec_ref(v_ys_4437_);
    leanh::lean_dec_ref(v_xs_4436_);
    v_r_4442_ = leanh::lean_box((v_res_4441_) as usize);
    return v_r_4442_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4445_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4445_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4446_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0);
    v___x_4447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4447_, 0, v___x_4446_);
    return v___x_4447_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(
    mut v_00_u03b2_4448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1);
    return v___x_4449_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4450_ = l_Lean_Meta_DiscrTree_empty(leanh::lean_box(0));
    return v___x_4450_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(leanh::lean_box(0));
    return v___x_4451_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1,
    );
    v___x_4453_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0,
    );
    v___x_4454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4454_, 0, v___x_4453_);
    leanh::lean_ctor_set(v___x_4454_, 1, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default()
-> *mut leanh::LeanObject {
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2,
    );
    return v___x_4455_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems()
-> *mut leanh::LeanObject {
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
    return v___x_4456_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_x_4457_: *mut leanh::LeanObject,
    mut v_x_4458_: *mut leanh::LeanObject,
    mut v_x_4459_: *mut leanh::LeanObject,
    mut v_x_4460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4461_ = leanh::lean_ctor_get(v_x_4457_, 0);
                v_vs_4462_ = leanh::lean_ctor_get(v_x_4457_, 1);
                v_isSharedCheck_4486_ = (!leanh::lean_is_exclusive(v_x_4457_)) as u8;
                if v_isSharedCheck_4486_ == 0 {
                    v___x_4464_ = v_x_4457_;
                    v_isShared_4465_ = v_isSharedCheck_4486_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4462_);
                    leanh::lean_inc(v_ks_4461_);
                    leanh::lean_dec(v_x_4457_);
                    v___x_4464_ = leanh::lean_box(0);
                    v_isShared_4465_ = v_isSharedCheck_4486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4466_ = lean_array_get_size(v_ks_4461_);
                v___x_4467_ = lean_nat_dec_lt(v_x_4458_, v___x_4466_);
                if v___x_4467_ == 0 {
                    leanh::lean_dec(v_x_4458_);
                    v___x_4468_ = lean_array_push(v_ks_4461_, v_x_4459_);
                    v___x_4469_ = lean_array_push(v_vs_4462_, v_x_4460_);
                    if v_isShared_4465_ == 0 {
                        leanh::lean_ctor_set(v___x_4464_, 1, v___x_4469_);
                        leanh::lean_ctor_set(v___x_4464_, 0, v___x_4468_);
                        v___x_4471_ = v___x_4464_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4472_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4468_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4469_);
                        v___x_4471_ = v_reuseFailAlloc_4472_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4473_ = lean_array_fget_borrowed(v_ks_4461_, v_x_4458_);
                    v___x_4474_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4459_, v_k_x27_4473_);
                    if v___x_4474_ == 0 {
                        if v_isShared_4465_ == 0 {
                            v___x_4476_ = v___x_4464_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4480_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_ks_4461_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_vs_4462_);
                            v___x_4476_ = v_reuseFailAlloc_4480_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4481_ = lean_array_fset(v_ks_4461_, v_x_4458_, v_x_4459_);
                        v___x_4482_ = lean_array_fset(v_vs_4462_, v_x_4458_, v_x_4460_);
                        leanh::lean_dec(v_x_4458_);
                        if v_isShared_4465_ == 0 {
                            leanh::lean_ctor_set(v___x_4464_, 1, v___x_4482_);
                            leanh::lean_ctor_set(v___x_4464_, 0, v___x_4481_);
                            v___x_4484_ = v___x_4464_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4485_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4481_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 1, v___x_4482_);
                            v___x_4484_ = v_reuseFailAlloc_4485_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4471_;
            }
            3 => {
                v___x_4477_ = leanh::lean_unsigned_to_nat(1);
                v___x_4478_ = lean_nat_add(v_x_4458_, v___x_4477_);
                leanh::lean_dec(v_x_4458_);
                v_x_4457_ = v___x_4476_;
                v_x_4458_ = v___x_4478_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_n_4487_: *mut leanh::LeanObject,
    mut v_k_4488_: *mut leanh::LeanObject,
    mut v_v_4489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = leanh::lean_unsigned_to_nat(0);
    v___x_4491_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_4487_, v___x_4490_, v_k_4488_, v_v_4489_);
    return v___x_4491_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: usize = 0;
    let mut v___x_4494_: usize = 0;
    v___x_4492_ = 5usize;
    v___x_4493_ = 1usize;
    v___x_4494_ = lean_usize_shift_left(v___x_4493_, v___x_4492_);
    return v___x_4494_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_4495_: usize = 0;
    let mut v___x_4496_: usize = 0;
    let mut v___x_4497_: usize = 0;
    v___x_4495_ = 1usize;
    v___x_4496_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0);
    v___x_4497_ = lean_usize_sub(v___x_4496_, v___x_4495_);
    return v___x_4497_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4498_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(
    mut v_x_4499_: *mut leanh::LeanObject,
    mut v_x_4500_: usize,
    mut v_x_4501_: usize,
    mut v_x_4502_: *mut leanh::LeanObject,
    mut v_x_4503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: usize = 0;
    let mut v___x_4506_: usize = 0;
    let mut v___x_4507_: usize = 0;
    let mut v___x_4508_: usize = 0;
    let mut v_j_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4514_: u8 = 0;
    let mut v_v_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4529_: u8 = 0;
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_node_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v___x_4540_: usize = 0;
    let mut v___x_4541_: usize = 0;
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut v_unused_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4559_: u8 = 0;
    let mut v_ks_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: usize = 0;
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v_reuseFailAlloc_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4499_) == 0 {
                    v_es_4504_ = leanh::lean_ctor_get(v_x_4499_, 0);
                    v___x_4505_ = 5usize;
                    v___x_4506_ = 1usize;
                    v___x_4507_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4508_ = lean_usize_land(v_x_4500_, v___x_4507_);
                    v_j_4509_ = lean_usize_to_nat(v___x_4508_);
                    v___x_4510_ = lean_array_get_size(v_es_4504_);
                    v___x_4511_ = lean_nat_dec_lt(v_j_4509_, v___x_4510_);
                    if v___x_4511_ == 0 {
                        leanh::lean_dec(v_j_4509_);
                        leanh::lean_dec(v_x_4503_);
                        leanh::lean_dec(v_x_4502_);
                        return v_x_4499_;
                    } else {
                        leanh::lean_inc_ref(v_es_4504_);
                        v_isSharedCheck_4548_ = (!leanh::lean_is_exclusive(v_x_4499_)) as u8;
                        if v_isSharedCheck_4548_ == 0 {
                            v_unused_4549_ = leanh::lean_ctor_get(v_x_4499_, 0);
                            leanh::lean_dec(v_unused_4549_);
                            v___x_4513_ = v_x_4499_;
                            v_isShared_4514_ = v_isSharedCheck_4548_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4499_);
                            v___x_4513_ = leanh::lean_box(0);
                            v_isShared_4514_ = v_isSharedCheck_4548_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4550_ = leanh::lean_ctor_get(v_x_4499_, 0);
                    v_vs_4551_ = leanh::lean_ctor_get(v_x_4499_, 1);
                    v_isSharedCheck_4571_ = (!leanh::lean_is_exclusive(v_x_4499_)) as u8;
                    if v_isSharedCheck_4571_ == 0 {
                        v___x_4553_ = v_x_4499_;
                        v_isShared_4554_ = v_isSharedCheck_4571_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4551_);
                        leanh::lean_inc(v_ks_4550_);
                        leanh::lean_dec(v_x_4499_);
                        v___x_4553_ = leanh::lean_box(0);
                        v_isShared_4554_ = v_isSharedCheck_4571_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4515_ = lean_array_fget(v_es_4504_, v_j_4509_);
                v___x_4516_ = leanh::lean_box(0);
                v_xs_x27_4517_ = lean_array_fset(v_es_4504_, v_j_4509_, v___x_4516_);
                match leanh::lean_obj_tag(v_v_4515_) {
                    0 => {
                        v_key_4524_ = leanh::lean_ctor_get(v_v_4515_, 0);
                        v_val_4525_ = leanh::lean_ctor_get(v_v_4515_, 1);
                        v_isSharedCheck_4535_ = (!leanh::lean_is_exclusive(v_v_4515_)) as u8;
                        if v_isSharedCheck_4535_ == 0 {
                            v___x_4527_ = v_v_4515_;
                            v_isShared_4528_ = v_isSharedCheck_4535_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4525_);
                            leanh::lean_inc(v_key_4524_);
                            leanh::lean_dec(v_v_4515_);
                            v___x_4527_ = leanh::lean_box(0);
                            v_isShared_4528_ = v_isSharedCheck_4535_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4536_ = leanh::lean_ctor_get(v_v_4515_, 0);
                        v_isSharedCheck_4546_ = (!leanh::lean_is_exclusive(v_v_4515_)) as u8;
                        if v_isSharedCheck_4546_ == 0 {
                            v___x_4538_ = v_v_4515_;
                            v_isShared_4539_ = v_isSharedCheck_4546_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4536_);
                            leanh::lean_dec(v_v_4515_);
                            v___x_4538_ = leanh::lean_box(0);
                            v_isShared_4539_ = v_isSharedCheck_4546_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4547_, 0, v_x_4502_);
                        leanh::lean_ctor_set(v___x_4547_, 1, v_x_4503_);
                        v___y_4519_ = v___x_4547_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4520_ = lean_array_fset(v_xs_x27_4517_, v_j_4509_, v___y_4519_);
                leanh::lean_dec(v_j_4509_);
                if v_isShared_4514_ == 0 {
                    leanh::lean_ctor_set(v___x_4513_, 0, v___x_4520_);
                    v___x_4522_ = v___x_4513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
                    v___x_4522_ = v_reuseFailAlloc_4523_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4522_;
            }
            4 => {
                v___x_4529_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4502_, v_key_4524_);
                if v___x_4529_ == 0 {
                    leanh::lean_del_object(v___x_4527_);
                    v___x_4530_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4524_,
                        v_val_4525_,
                        v_x_4502_,
                        v_x_4503_,
                    );
                    v___x_4531_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4531_, 0, v___x_4530_);
                    v___y_4519_ = v___x_4531_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4525_);
                    leanh::lean_dec(v_key_4524_);
                    if v_isShared_4528_ == 0 {
                        leanh::lean_ctor_set(v___x_4527_, 1, v_x_4503_);
                        leanh::lean_ctor_set(v___x_4527_, 0, v_x_4502_);
                        v___x_4533_ = v___x_4527_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_x_4502_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_x_4503_);
                        v___x_4533_ = v_reuseFailAlloc_4534_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4519_ = v___x_4533_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4540_ = lean_usize_shift_right(v_x_4500_, v___x_4505_);
                v___x_4541_ = lean_usize_add(v_x_4501_, v___x_4506_);
                v___x_4542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_node_4536_, v___x_4540_, v___x_4541_, v_x_4502_, v_x_4503_);
                if v_isShared_4539_ == 0 {
                    leanh::lean_ctor_set(v___x_4538_, 0, v___x_4542_);
                    v___x_4544_ = v___x_4538_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
                    v___x_4544_ = v_reuseFailAlloc_4545_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4519_ = v___x_4544_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4554_ == 0 {
                    v___x_4556_ = v___x_4553_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_ks_4550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_vs_4551_);
                    v___x_4556_ = v_reuseFailAlloc_4570_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4557_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v___x_4556_, v_x_4502_, v_x_4503_);
                v___x_4565_ = 7usize;
                v___x_4566_ = lean_usize_dec_le(v___x_4565_, v_x_4501_);
                if v___x_4566_ == 0 {
                    v___x_4567_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4557_);
                    v___x_4568_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4569_ = lean_nat_dec_lt(v___x_4567_, v___x_4568_);
                    leanh::lean_dec(v___x_4567_);
                    v___y_4559_ = v___x_4569_;
                    state = 10;
                    continue;
                } else {
                    v___y_4559_ = v___x_4566_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4559_ == 0 {
                    v_ks_4560_ = leanh::lean_ctor_get(v_newNode_4557_, 0);
                    leanh::lean_inc_ref(v_ks_4560_);
                    v_vs_4561_ = leanh::lean_ctor_get(v_newNode_4557_, 1);
                    leanh::lean_inc_ref(v_vs_4561_);
                    leanh::lean_dec_ref(v_newNode_4557_);
                    v___x_4562_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4563_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2);
                    v___x_4564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4501_, v_ks_4560_, v_vs_4561_, v___x_4562_, v___x_4563_);
                    leanh::lean_dec_ref(v_vs_4561_);
                    leanh::lean_dec_ref(v_ks_4560_);
                    return v___x_4564_;
                } else {
                    return v_newNode_4557_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_depth_4572_: usize,
    mut v_keys_4573_: *mut leanh::LeanObject,
    mut v_vals_4574_: *mut leanh::LeanObject,
    mut v_i_4575_: *mut leanh::LeanObject,
    mut v_entries_4576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v_k_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u64 = 0;
    let mut v_h_4582_: usize = 0;
    let mut v___x_4583_: usize = 0;
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: usize = 0;
    let mut v___x_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v_h_4588_: usize = 0;
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4577_ = lean_array_get_size(v_keys_4573_);
                v___x_4578_ = lean_nat_dec_lt(v_i_4575_, v___x_4577_);
                if v___x_4578_ == 0 {
                    leanh::lean_dec(v_i_4575_);
                    return v_entries_4576_;
                } else {
                    v_k_4579_ = lean_array_fget_borrowed(v_keys_4573_, v_i_4575_);
                    v_v_4580_ = lean_array_fget_borrowed(v_vals_4574_, v_i_4575_);
                    v___x_4581_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_4579_);
                    v_h_4582_ = lean_uint64_to_usize(v___x_4581_);
                    v___x_4583_ = 5usize;
                    v___x_4584_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4585_ = 1usize;
                    v___x_4586_ = lean_usize_sub(v_depth_4572_, v___x_4585_);
                    v___x_4587_ = lean_usize_mul(v___x_4583_, v___x_4586_);
                    v_h_4588_ = lean_usize_shift_right(v_h_4582_, v___x_4587_);
                    v___x_4589_ = lean_nat_add(v_i_4575_, v___x_4584_);
                    leanh::lean_dec(v_i_4575_);
                    leanh::lean_inc(v_v_4580_);
                    leanh::lean_inc(v_k_4579_);
                    v___x_4590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_entries_4576_, v_h_4588_, v_depth_4572_, v_k_4579_, v_v_4580_);
                    v_i_4575_ = v___x_4589_;
                    v_entries_4576_ = v___x_4590_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_depth_4592_: *mut leanh::LeanObject,
    mut v_keys_4593_: *mut leanh::LeanObject,
    mut v_vals_4594_: *mut leanh::LeanObject,
    mut v_i_4595_: *mut leanh::LeanObject,
    mut v_entries_4596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4597_: usize = 0;
    let mut v_res_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4597_ = leanh::lean_unbox_usize(v_depth_4592_);
    leanh::lean_dec(v_depth_4592_);
    v_res_4598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_4597_, v_keys_4593_, v_vals_4594_, v_i_4595_, v_entries_4596_);
    leanh::lean_dec_ref(v_vals_4594_);
    leanh::lean_dec_ref(v_keys_4593_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_4599_: *mut leanh::LeanObject,
    mut v_x_4600_: *mut leanh::LeanObject,
    mut v_x_4601_: *mut leanh::LeanObject,
    mut v_x_4602_: *mut leanh::LeanObject,
    mut v_x_4603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1605__boxed_4604_: usize = 0;
    let mut v_x_1606__boxed_4605_: usize = 0;
    let mut v_res_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1605__boxed_4604_ = leanh::lean_unbox_usize(v_x_4600_);
    leanh::lean_dec(v_x_4600_);
    v_x_1606__boxed_4605_ = leanh::lean_unbox_usize(v_x_4601_);
    leanh::lean_dec(v_x_4601_);
    v_res_4606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_4599_, v_x_1605__boxed_4604_, v_x_1606__boxed_4605_, v_x_4602_, v_x_4603_);
    return v_res_4606_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(
    mut v_x_4607_: *mut leanh::LeanObject,
    mut v_x_4608_: *mut leanh::LeanObject,
    mut v_x_4609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4610_: u64 = 0;
    let mut v___x_4611_: usize = 0;
    let mut v___x_4612_: usize = 0;
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4608_);
    v___x_4611_ = lean_uint64_to_usize(v___x_4610_);
    v___x_4612_ = 1usize;
    v___x_4613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_4607_, v___x_4611_, v___x_4612_, v_x_4608_, v_x_4609_);
    return v___x_4613_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(
    mut v_vs_4614_: *mut leanh::LeanObject,
    mut v_v_4615_: *mut leanh::LeanObject,
    mut v_i_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4617_ = lean_array_get_size(v_vs_4614_);
                v___x_4618_ = lean_nat_dec_lt(v_i_4616_, v___x_4617_);
                if v___x_4618_ == 0 {
                    leanh::lean_dec(v_i_4616_);
                    v___x_4619_ = lean_array_push(v_vs_4614_, v_v_4615_);
                    return v___x_4619_;
                } else {
                    v___x_4620_ = lean_array_fget_borrowed(v_vs_4614_, v_i_4616_);
                    leanh::lean_inc(v___x_4620_);
                    leanh::lean_inc_ref(v_v_4615_);
                    v___x_4621_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(
                        v_v_4615_,
                        v___x_4620_,
                    );
                    if v___x_4621_ == 0 {
                        v___x_4622_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4623_ = lean_nat_add(v_i_4616_, v___x_4622_);
                        leanh::lean_dec(v_i_4616_);
                        v_i_4616_ = v___x_4623_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4625_ = lean_array_fset(v_vs_4614_, v_i_4616_, v_v_4615_);
                        leanh::lean_dec(v_i_4616_);
                        return v___x_4625_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(
    mut v_vs_4626_: *mut leanh::LeanObject,
    mut v_v_4627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = leanh::lean_unsigned_to_nat(0);
    v___x_4629_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(v_vs_4626_, v_v_4627_, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(
    mut v_a_4630_: *mut leanh::LeanObject,
    mut v_b_4631_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    v_fst_4632_ = leanh::lean_ctor_get(v_a_4630_, 0);
    v_fst_4633_ = leanh::lean_ctor_get(v_b_4631_, 0);
    v___x_4634_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_4632_, v_fst_4633_);
    return v___x_4634_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1___boxed(
    mut v_a_4635_: *mut leanh::LeanObject,
    mut v_b_4636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4637_: u8 = 0;
    let mut v_r_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4637_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_a_4635_, v_b_4636_);
    leanh::lean_dec_ref(v_b_4636_);
    leanh::lean_dec_ref(v_a_4635_);
    v_r_4638_ = leanh::lean_box((v_res_4637_) as usize);
    return v_r_4638_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(
    mut v_x_4639_: *mut leanh::LeanObject,
    mut v_keys_4640_: *mut leanh::LeanObject,
    mut v_v_4641_: *mut leanh::LeanObject,
    mut v_k_4642_: *mut leanh::LeanObject,
    mut v_x_4643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = leanh::lean_unsigned_to_nat(1);
    v___x_4645_ = lean_nat_add(v_x_4639_, v___x_4644_);
    v_c_4646_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        leanh::lean_box(0),
        v_keys_4640_,
        v_v_4641_,
        v___x_4645_,
    );
    leanh::lean_dec(v___x_4645_);
    v___x_4647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4647_, 0, v_k_4642_);
    leanh::lean_ctor_set(v___x_4647_, 1, v_c_4646_);
    return v___x_4647_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0___boxed(
    mut v_x_4648_: *mut leanh::LeanObject,
    mut v_keys_4649_: *mut leanh::LeanObject,
    mut v_v_4650_: *mut leanh::LeanObject,
    mut v_k_4651_: *mut leanh::LeanObject,
    mut v_x_4652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4648_, v_keys_4649_, v_v_4650_, v_k_4651_, v_x_4652_);
    leanh::lean_dec_ref(v_keys_4649_);
    leanh::lean_dec(v_x_4648_);
    return v_res_4653_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_x_4658_: *mut leanh::LeanObject,
    mut v_keys_4659_: *mut leanh::LeanObject,
    mut v_v_4660_: *mut leanh::LeanObject,
    mut v_k_4661_: *mut leanh::LeanObject,
    mut v_as_4662_: *mut leanh::LeanObject,
    mut v_k_4663_: *mut leanh::LeanObject,
    mut v_x_4664_: *mut leanh::LeanObject,
    mut v_x_4665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: u8 = 0;
    let mut v_snd_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut v_unused_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: u8 = 0;
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4666_ = lean_nat_add(v_x_4664_, v_x_4665_);
                v___x_4667_ = leanh::lean_unsigned_to_nat(1);
                v_mid_4668_ = lean_nat_shiftr(v___x_4666_, v___x_4667_);
                leanh::lean_dec(v___x_4666_);
                v_midVal_4669_ = lean_array_fget(v_as_4662_, v_mid_4668_);
                v___x_4670_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_midVal_4669_, v_k_4663_);
                if v___x_4670_ == 0 {
                    leanh::lean_dec(v_x_4665_);
                    v___x_4671_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_4663_, v_midVal_4669_);
                    if v___x_4671_ == 0 {
                        leanh::lean_dec(v_x_4664_);
                        v___x_4672_ = lean_array_get_size(v_as_4662_);
                        v___x_4673_ = lean_nat_dec_lt(v_mid_4668_, v___x_4672_);
                        if v___x_4673_ == 0 {
                            leanh::lean_dec(v_midVal_4669_);
                            leanh::lean_dec(v_mid_4668_);
                            leanh::lean_dec(v_k_4661_);
                            leanh::lean_dec_ref(v_v_4660_);
                            return v_as_4662_;
                        } else {
                            v_snd_4674_ = leanh::lean_ctor_get(v_midVal_4669_, 1);
                            v_isSharedCheck_4686_ =
                                (!leanh::lean_is_exclusive(v_midVal_4669_)) as u8;
                            if v_isSharedCheck_4686_ == 0 {
                                v_unused_4687_ = leanh::lean_ctor_get(v_midVal_4669_, 0);
                                leanh::lean_dec(v_unused_4687_);
                                v___x_4676_ = v_midVal_4669_;
                                v_isShared_4677_ = v_isSharedCheck_4686_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_4674_);
                                leanh::lean_dec(v_midVal_4669_);
                                v___x_4676_ = leanh::lean_box(0);
                                v_isShared_4677_ = v_isSharedCheck_4686_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_midVal_4669_);
                        v_x_4665_ = v_mid_4668_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_midVal_4669_);
                    v___x_4689_ = lean_nat_dec_eq(v_mid_4668_, v_x_4664_);
                    if v___x_4689_ == 0 {
                        leanh::lean_dec(v_x_4664_);
                        v_x_4664_ = v_mid_4668_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_mid_4668_);
                        leanh::lean_dec(v_x_4665_);
                        v___x_4691_ = lean_nat_add(v_x_4658_, v___x_4667_);
                        v_c_4692_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(leanh::lean_box(0), v_keys_4659_, v_v_4660_, v___x_4691_);
                        leanh::lean_dec(v___x_4691_);
                        v___x_4693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4693_, 0, v_k_4661_);
                        leanh::lean_ctor_set(v___x_4693_, 1, v_c_4692_);
                        v___x_4694_ = lean_nat_add(v_x_4664_, v___x_4667_);
                        leanh::lean_dec(v_x_4664_);
                        v_j_4695_ = lean_array_get_size(v_as_4662_);
                        v_as_4696_ = lean_array_push(v_as_4662_, v___x_4693_);
                        v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            leanh::lean_box(0),
                            v___x_4694_,
                            v_as_4696_,
                            v_j_4695_,
                        );
                        leanh::lean_dec(v___x_4694_);
                        return v___x_4697_;
                    }
                }
            }
            1 => {
                v___x_4678_ = leanh::lean_box(0);
                v_xs_x27_4679_ = lean_array_fset(v_as_4662_, v_mid_4668_, v___x_4678_);
                v___x_4680_ = lean_nat_add(v_x_4658_, v___x_4667_);
                v_c_4681_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4659_, v_v_4660_, v___x_4680_, v_snd_4674_);
                leanh::lean_dec(v___x_4680_);
                if v_isShared_4677_ == 0 {
                    leanh::lean_ctor_set(v___x_4676_, 1, v_c_4681_);
                    leanh::lean_ctor_set(v___x_4676_, 0, v_k_4661_);
                    v___x_4683_ = v___x_4676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_k_4661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_c_4681_);
                    v___x_4683_ = v_reuseFailAlloc_4685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4684_ = lean_array_fset(v_xs_x27_4679_, v_mid_4668_, v___x_4683_);
                leanh::lean_dec(v_mid_4668_);
                return v___x_4684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(
    mut v_x_4698_: *mut leanh::LeanObject,
    mut v_keys_4699_: *mut leanh::LeanObject,
    mut v_v_4700_: *mut leanh::LeanObject,
    mut v_k_4701_: *mut leanh::LeanObject,
    mut v_as_4702_: *mut leanh::LeanObject,
    mut v_k_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: u8 = 0;
    v___x_4704_ = lean_array_get_size(v_as_4702_);
    v___x_4705_ = leanh::lean_unsigned_to_nat(0);
    v___x_4706_ = lean_nat_dec_eq(v___x_4704_, v___x_4705_);
    if v___x_4706_ == 0 {
        let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4708_: u8 = 0;
        v___x_4707_ = lean_array_fget_borrowed(v_as_4702_, v___x_4705_);
        v___x_4708_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_4703_, v___x_4707_);
        if v___x_4708_ == 0 {
            let mut v___x_4709_: u8 = 0;
            v___x_4709_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v___x_4707_, v_k_4703_);
            if v___x_4709_ == 0 {
                let mut v___x_4710_: u8 = 0;
                v___x_4710_ = lean_nat_dec_lt(v___x_4705_, v___x_4704_);
                if v___x_4710_ == 0 {
                    leanh::lean_dec(v_k_4701_);
                    leanh::lean_dec_ref(v_v_4700_);
                    return v_as_4702_;
                } else {
                    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc(v___x_4707_);
                    v___x_4711_ = leanh::lean_box(0);
                    v_xs_x27_4712_ = lean_array_fset(v_as_4702_, v___x_4705_, v___x_4711_);
                    v___x_4713_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4707_);
                    v___x_4714_ = lean_array_fset(v_xs_x27_4712_, v___x_4705_, v___x_4713_);
                    return v___x_4714_;
                }
            } else {
                let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4718_: u8 = 0;
                v___x_4715_ = leanh::lean_unsigned_to_nat(1);
                v___x_4716_ = lean_nat_sub(v___x_4704_, v___x_4715_);
                v___x_4717_ = lean_array_fget_borrowed(v_as_4702_, v___x_4716_);
                v___x_4718_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v___x_4717_, v_k_4703_);
                if v___x_4718_ == 0 {
                    let mut v___x_4719_: u8 = 0;
                    v___x_4719_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_4703_, v___x_4717_);
                    if v___x_4719_ == 0 {
                        let mut v___x_4720_: u8 = 0;
                        v___x_4720_ = lean_nat_dec_lt(v___x_4716_, v___x_4704_);
                        if v___x_4720_ == 0 {
                            leanh::lean_dec(v___x_4716_);
                            leanh::lean_dec(v_k_4701_);
                            leanh::lean_dec_ref(v_v_4700_);
                            return v_as_4702_;
                        } else {
                            let mut v___x_4721_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_4722_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4723_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4724_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_inc(v___x_4717_);
                            v___x_4721_ = leanh::lean_box(0);
                            v_xs_x27_4722_ = lean_array_fset(v_as_4702_, v___x_4716_, v___x_4721_);
                            v___x_4723_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4717_);
                            v___x_4724_ = lean_array_fset(v_xs_x27_4722_, v___x_4716_, v___x_4723_);
                            leanh::lean_dec(v___x_4716_);
                            return v___x_4724_;
                        }
                    } else {
                        let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4725_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v_as_4702_, v_k_4703_, v___x_4705_, v___x_4716_);
                        return v___x_4725_;
                    }
                } else {
                    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_4716_);
                    v___x_4726_ = leanh::lean_box(0);
                    v___x_4727_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4726_);
                    v___x_4728_ = lean_array_push(v_as_4702_, v___x_4727_);
                    return v___x_4728_;
                }
            }
        } else {
            let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_as_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4729_ = leanh::lean_box(0);
            v___x_4730_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4729_);
            v_as_4731_ = lean_array_push(v_as_4702_, v___x_4730_);
            v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                leanh::lean_box(0),
                v___x_4705_,
                v_as_4731_,
                v___x_4704_,
            );
            return v___x_4732_;
        }
    } else {
        let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4733_ = leanh::lean_box(0);
        v___x_4734_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4733_);
        v___x_4735_ = lean_array_push(v_as_4702_, v___x_4734_);
        return v___x_4735_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(
    mut v_keys_4736_: *mut leanh::LeanObject,
    mut v_v_4737_: *mut leanh::LeanObject,
    mut v_x_4738_: *mut leanh::LeanObject,
    mut v_x_4739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_4740_ = leanh::lean_ctor_get(v_x_4739_, 0);
                v_children_4741_ = leanh::lean_ctor_get(v_x_4739_, 1);
                v_isSharedCheck_4758_ = (!leanh::lean_is_exclusive(v_x_4739_)) as u8;
                if v_isSharedCheck_4758_ == 0 {
                    v___x_4743_ = v_x_4739_;
                    v_isShared_4744_ = v_isSharedCheck_4758_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_children_4741_);
                    leanh::lean_inc(v_vs_4740_);
                    leanh::lean_dec(v_x_4739_);
                    v___x_4743_ = leanh::lean_box(0);
                    v_isShared_4744_ = v_isSharedCheck_4758_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4745_ = lean_array_get_size(v_keys_4736_);
                v___x_4746_ = lean_nat_dec_lt(v_x_4738_, v___x_4745_);
                if v___x_4746_ == 0 {
                    v___x_4747_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(v_vs_4740_, v_v_4737_);
                    if v_isShared_4744_ == 0 {
                        leanh::lean_ctor_set(v___x_4743_, 0, v___x_4747_);
                        v___x_4749_ = v___x_4743_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4750_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_children_4741_);
                        v___x_4749_ = v_reuseFailAlloc_4750_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_4751_ = lean_array_fget_borrowed(v_keys_4736_, v_x_4738_);
                    v___x_4752_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1;
                    leanh::lean_inc_n(v_k_4751_, 2);
                    v___x_4753_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4753_, 0, v_k_4751_);
                    leanh::lean_ctor_set(v___x_4753_, 1, v___x_4752_);
                    v_c_4754_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_4738_, v_keys_4736_, v_v_4737_, v_k_4751_, v_children_4741_, v___x_4753_);
                    leanh::lean_dec_ref_known(v___x_4753_, 2);
                    if v_isShared_4744_ == 0 {
                        leanh::lean_ctor_set(v___x_4743_, 1, v_c_4754_);
                        v___x_4756_ = v___x_4743_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4757_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_vs_4740_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_c_4754_);
                        v___x_4756_ = v_reuseFailAlloc_4757_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4749_;
            }
            3 => {
                return v___x_4756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(
    mut v_x_4759_: *mut leanh::LeanObject,
    mut v_keys_4760_: *mut leanh::LeanObject,
    mut v_v_4761_: *mut leanh::LeanObject,
    mut v_k_4762_: *mut leanh::LeanObject,
    mut v_x_4763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_unused_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4764_ = leanh::lean_ctor_get(v_x_4763_, 1);
                v_isSharedCheck_4774_ = (!leanh::lean_is_exclusive(v_x_4763_)) as u8;
                if v_isSharedCheck_4774_ == 0 {
                    v_unused_4775_ = leanh::lean_ctor_get(v_x_4763_, 0);
                    leanh::lean_dec(v_unused_4775_);
                    v___x_4766_ = v_x_4763_;
                    v_isShared_4767_ = v_isSharedCheck_4774_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4764_);
                    leanh::lean_dec(v_x_4763_);
                    v___x_4766_ = leanh::lean_box(0);
                    v_isShared_4767_ = v_isSharedCheck_4774_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4768_ = leanh::lean_unsigned_to_nat(1);
                v___x_4769_ = lean_nat_add(v_x_4759_, v___x_4768_);
                v_c_4770_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4760_, v_v_4761_, v___x_4769_, v_snd_4764_);
                leanh::lean_dec(v___x_4769_);
                if v_isShared_4767_ == 0 {
                    leanh::lean_ctor_set(v___x_4766_, 1, v_c_4770_);
                    leanh::lean_ctor_set(v___x_4766_, 0, v_k_4762_);
                    v___x_4772_ = v___x_4766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_k_4762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_c_4770_);
                    v___x_4772_ = v_reuseFailAlloc_4773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2___boxed(
    mut v_x_4776_: *mut leanh::LeanObject,
    mut v_keys_4777_: *mut leanh::LeanObject,
    mut v_v_4778_: *mut leanh::LeanObject,
    mut v_k_4779_: *mut leanh::LeanObject,
    mut v_x_4780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_4776_, v_keys_4777_, v_v_4778_, v_k_4779_, v_x_4780_);
    leanh::lean_dec_ref(v_keys_4777_);
    leanh::lean_dec(v_x_4776_);
    return v_res_4781_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___boxed(
    mut v_keys_4782_: *mut leanh::LeanObject,
    mut v_v_4783_: *mut leanh::LeanObject,
    mut v_x_4784_: *mut leanh::LeanObject,
    mut v_x_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4786_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4782_, v_v_4783_, v_x_4784_, v_x_4785_);
    leanh::lean_dec(v_x_4784_);
    leanh::lean_dec_ref(v_keys_4782_);
    return v_res_4786_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_x_4787_: *mut leanh::LeanObject,
    mut v_keys_4788_: *mut leanh::LeanObject,
    mut v_v_4789_: *mut leanh::LeanObject,
    mut v_k_4790_: *mut leanh::LeanObject,
    mut v_as_4791_: *mut leanh::LeanObject,
    mut v_k_4792_: *mut leanh::LeanObject,
    mut v_x_4793_: *mut leanh::LeanObject,
    mut v_x_4794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4795_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_4787_, v_keys_4788_, v_v_4789_, v_k_4790_, v_as_4791_, v_k_4792_, v_x_4793_, v_x_4794_);
    leanh::lean_dec_ref(v_k_4792_);
    leanh::lean_dec_ref(v_keys_4788_);
    leanh::lean_dec(v_x_4787_);
    return v_res_4795_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___boxed(
    mut v_x_4796_: *mut leanh::LeanObject,
    mut v_keys_4797_: *mut leanh::LeanObject,
    mut v_v_4798_: *mut leanh::LeanObject,
    mut v_k_4799_: *mut leanh::LeanObject,
    mut v_as_4800_: *mut leanh::LeanObject,
    mut v_k_4801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_4796_, v_keys_4797_, v_v_4798_, v_k_4799_, v_as_4800_, v_k_4801_);
    leanh::lean_dec_ref(v_k_4801_);
    leanh::lean_dec_ref(v_keys_4797_);
    leanh::lean_dec(v_x_4796_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_4803_: *mut leanh::LeanObject,
    mut v_vals_4804_: *mut leanh::LeanObject,
    mut v_i_4805_: *mut leanh::LeanObject,
    mut v_k_4806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: u8 = 0;
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4807_ = lean_array_get_size(v_keys_4803_);
                v___x_4808_ = lean_nat_dec_lt(v_i_4805_, v___x_4807_);
                if v___x_4808_ == 0 {
                    leanh::lean_dec(v_i_4805_);
                    v___x_4809_ = leanh::lean_box(0);
                    return v___x_4809_;
                } else {
                    v_k_x27_4810_ = lean_array_fget_borrowed(v_keys_4803_, v_i_4805_);
                    v___x_4811_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_4806_, v_k_x27_4810_);
                    if v___x_4811_ == 0 {
                        v___x_4812_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4813_ = lean_nat_add(v_i_4805_, v___x_4812_);
                        leanh::lean_dec(v_i_4805_);
                        v_i_4805_ = v___x_4813_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4815_ = lean_array_fget_borrowed(v_vals_4804_, v_i_4805_);
                        leanh::lean_dec(v_i_4805_);
                        leanh::lean_inc(v___x_4815_);
                        v___x_4816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4816_, 0, v___x_4815_);
                        return v___x_4816_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_4817_: *mut leanh::LeanObject,
    mut v_vals_4818_: *mut leanh::LeanObject,
    mut v_i_4819_: *mut leanh::LeanObject,
    mut v_k_4820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4821_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_4817_, v_vals_4818_, v_i_4819_, v_k_4820_);
    leanh::lean_dec(v_k_4820_);
    leanh::lean_dec_ref(v_vals_4818_);
    leanh::lean_dec_ref(v_keys_4817_);
    return v_res_4821_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(
    mut v_x_4822_: *mut leanh::LeanObject,
    mut v_x_4823_: usize,
    mut v_x_4824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4829_: usize = 0;
    let mut v_j_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: u8 = 0;
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: usize = 0;
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4822_) == 0 {
                    v_es_4825_ = leanh::lean_ctor_get(v_x_4822_, 0);
                    v___x_4826_ = leanh::lean_box(2);
                    v___x_4827_ = 5usize;
                    v___x_4828_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4829_ = lean_usize_land(v_x_4823_, v___x_4828_);
                    v_j_4830_ = lean_usize_to_nat(v___x_4829_);
                    v___x_4831_ = lean_array_get_borrowed(v___x_4826_, v_es_4825_, v_j_4830_);
                    leanh::lean_dec(v_j_4830_);
                    match leanh::lean_obj_tag(v___x_4831_) {
                        0 => {
                            v_key_4832_ = leanh::lean_ctor_get(v___x_4831_, 0);
                            v_val_4833_ = leanh::lean_ctor_get(v___x_4831_, 1);
                            v___x_4834_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4824_, v_key_4832_);
                            if v___x_4834_ == 0 {
                                v___x_4835_ = leanh::lean_box(0);
                                return v___x_4835_;
                            } else {
                                leanh::lean_inc(v_val_4833_);
                                v___x_4836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4836_, 0, v_val_4833_);
                                return v___x_4836_;
                            }
                        }
                        1 => {
                            v_node_4837_ = leanh::lean_ctor_get(v___x_4831_, 0);
                            v___x_4838_ = lean_usize_shift_right(v_x_4823_, v___x_4827_);
                            v_x_4822_ = v_node_4837_;
                            v_x_4823_ = v___x_4838_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4840_ = leanh::lean_box(0);
                            return v___x_4840_;
                        }
                    }
                } else {
                    v_ks_4841_ = leanh::lean_ctor_get(v_x_4822_, 0);
                    v_vs_4842_ = leanh::lean_ctor_get(v_x_4822_, 1);
                    v___x_4843_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4844_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_4841_, v_vs_4842_, v___x_4843_, v_x_4824_);
                    return v___x_4844_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4845_: *mut leanh::LeanObject,
    mut v_x_4846_: *mut leanh::LeanObject,
    mut v_x_4847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2045__boxed_4848_: usize = 0;
    let mut v_res_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2045__boxed_4848_ = leanh::lean_unbox_usize(v_x_4846_);
    leanh::lean_dec(v_x_4846_);
    v_res_4849_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_4845_, v_x_2045__boxed_4848_, v_x_4847_);
    leanh::lean_dec(v_x_4847_);
    leanh::lean_dec_ref(v_x_4845_);
    return v_res_4849_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(
    mut v_x_4850_: *mut leanh::LeanObject,
    mut v_x_4851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4852_: u64 = 0;
    let mut v___x_4853_: usize = 0;
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4852_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4851_);
    v___x_4853_ = lean_uint64_to_usize(v___x_4852_);
    v___x_4854_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_4850_, v___x_4853_, v_x_4851_);
    return v___x_4854_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_4855_: *mut leanh::LeanObject,
    mut v_x_4856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4857_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_4855_, v_x_4856_);
    leanh::lean_dec(v_x_4856_);
    leanh::lean_dec_ref(v_x_4855_);
    return v_res_4857_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4858_ = l_Lean_Meta_DiscrTree_instInhabited(leanh::lean_box(0));
    return v___x_4858_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(
    mut v_msg_4859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0);
    v___x_4861_ = lean_panic_fn_borrowed(v___x_4860_, v_msg_4859_);
    return v___x_4861_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4865_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2;
    v___x_4866_ = leanh::lean_unsigned_to_nat(23);
    v___x_4867_ = leanh::lean_unsigned_to_nat(166);
    v___x_4868_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1;
    v___x_4869_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0;
    v___x_4870_ = l_mkPanicMessageWithDecl(
        v___x_4869_,
        v___x_4868_,
        v___x_4867_,
        v___x_4866_,
        v___x_4865_,
    );
    return v___x_4870_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(
    mut v_d_4871_: *mut leanh::LeanObject,
    mut v_keys_4872_: *mut leanh::LeanObject,
    mut v_v_4873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    v___x_4874_ = lean_array_get_size(v_keys_4872_);
    v___x_4875_ = leanh::lean_unsigned_to_nat(0);
    v___x_4876_ = lean_nat_dec_eq(v___x_4874_, v___x_4875_);
    if v___x_4876_ == 0 {
        let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4877_ = leanh::lean_box(0);
        v_k_4878_ = lean_array_get_borrowed(v___x_4877_, v_keys_4872_, v___x_4875_);
        v___x_4879_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_d_4871_, v_k_4878_);
        if leanh::lean_obj_tag(v___x_4879_) == 0 {
            let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4880_ = leanh::lean_unsigned_to_nat(1);
            v_c_4881_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                leanh::lean_box(0),
                v_keys_4872_,
                v_v_4873_,
                v___x_4880_,
            );
            leanh::lean_inc(v_k_4878_);
            v___x_4882_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_4871_, v_k_4878_, v_c_4881_);
            return v___x_4882_;
        } else {
            let mut v_val_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_4883_ = leanh::lean_ctor_get(v___x_4879_, 0);
            leanh::lean_inc(v_val_4883_);
            leanh::lean_dec_ref_known(v___x_4879_, 1);
            v___x_4884_ = leanh::lean_unsigned_to_nat(1);
            v_c_4885_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4872_, v_v_4873_, v___x_4884_, v_val_4883_);
            leanh::lean_inc(v_k_4878_);
            v___x_4886_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_4871_, v_k_4878_, v_c_4885_);
            return v___x_4886_;
        }
    } else {
        let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_v_4873_);
        leanh::lean_dec_ref(v_d_4871_);
        v___x_4887_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3);
        v___x_4888_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(v___x_4887_);
        return v___x_4888_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___boxed(
    mut v_d_4889_: *mut leanh::LeanObject,
    mut v_keys_4890_: *mut leanh::LeanObject,
    mut v_v_4891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_d_4889_, v_keys_4890_, v_v_4891_);
    leanh::lean_dec_ref(v_keys_4890_);
    return v_res_4892_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(
    mut v_d_4893_: *mut leanh::LeanObject,
    mut v_e_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_specs_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v_keys_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_4895_ = leanh::lean_ctor_get(v_d_4893_, 0);
                v_erased_4896_ = leanh::lean_ctor_get(v_d_4893_, 1);
                v_isSharedCheck_4905_ = (!leanh::lean_is_exclusive(v_d_4893_)) as u8;
                if v_isSharedCheck_4905_ == 0 {
                    v___x_4898_ = v_d_4893_;
                    v_isShared_4899_ = v_isSharedCheck_4905_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_4896_);
                    leanh::lean_inc(v_specs_4895_);
                    leanh::lean_dec(v_d_4893_);
                    v___x_4898_ = leanh::lean_box(0);
                    v_isShared_4899_ = v_isSharedCheck_4905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keys_4900_ = leanh::lean_ctor_get(v_e_4894_, 0);
                leanh::lean_inc_ref(v_keys_4900_);
                v___x_4901_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_specs_4895_, v_keys_4900_, v_e_4894_);
                leanh::lean_dec_ref(v_keys_4900_);
                if v_isShared_4899_ == 0 {
                    leanh::lean_ctor_set(v___x_4898_, 0, v___x_4901_);
                    v___x_4903_ = v___x_4898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_erased_4896_);
                    v___x_4903_ = v_reuseFailAlloc_4904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(
    mut v_00_u03b2_4906_: *mut leanh::LeanObject,
    mut v_x_4907_: *mut leanh::LeanObject,
    mut v_x_4908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4909_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_4907_, v_x_4908_);
    return v___x_4909_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_4910_: *mut leanh::LeanObject,
    mut v_x_4911_: *mut leanh::LeanObject,
    mut v_x_4912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_00_u03b2_4910_, v_x_4911_, v_x_4912_);
    leanh::lean_dec(v_x_4912_);
    leanh::lean_dec_ref(v_x_4911_);
    return v_res_4913_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(
    mut v_00_u03b2_4914_: *mut leanh::LeanObject,
    mut v_x_4915_: *mut leanh::LeanObject,
    mut v_x_4916_: *mut leanh::LeanObject,
    mut v_x_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4918_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_x_4915_, v_x_4916_, v_x_4917_);
    return v___x_4918_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4919_: *mut leanh::LeanObject,
    mut v_x_4920_: *mut leanh::LeanObject,
    mut v_x_4921_: usize,
    mut v_x_4922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_4920_, v_x_4921_, v_x_4922_);
    return v___x_4923_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4924_: *mut leanh::LeanObject,
    mut v_x_4925_: *mut leanh::LeanObject,
    mut v_x_4926_: *mut leanh::LeanObject,
    mut v_x_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2196__boxed_4928_: usize = 0;
    let mut v_res_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2196__boxed_4928_ = leanh::lean_unbox_usize(v_x_4926_);
    leanh::lean_dec(v_x_4926_);
    v_res_4929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_00_u03b2_4924_, v_x_4925_, v_x_2196__boxed_4928_, v_x_4927_);
    leanh::lean_dec(v_x_4927_);
    leanh::lean_dec_ref(v_x_4925_);
    return v_res_4929_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4930_: *mut leanh::LeanObject,
    mut v_x_4931_: *mut leanh::LeanObject,
    mut v_x_4932_: usize,
    mut v_x_4933_: usize,
    mut v_x_4934_: *mut leanh::LeanObject,
    mut v_x_4935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_4931_, v_x_4932_, v_x_4933_, v_x_4934_, v_x_4935_);
    return v___x_4936_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4937_: *mut leanh::LeanObject,
    mut v_x_4938_: *mut leanh::LeanObject,
    mut v_x_4939_: *mut leanh::LeanObject,
    mut v_x_4940_: *mut leanh::LeanObject,
    mut v_x_4941_: *mut leanh::LeanObject,
    mut v_x_4942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2207__boxed_4943_: usize = 0;
    let mut v_x_2208__boxed_4944_: usize = 0;
    let mut v_res_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2207__boxed_4943_ = leanh::lean_unbox_usize(v_x_4939_);
    leanh::lean_dec(v_x_4939_);
    v_x_2208__boxed_4944_ = leanh::lean_unbox_usize(v_x_4940_);
    leanh::lean_dec(v_x_4940_);
    v_res_4945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(v_00_u03b2_4937_, v_x_4938_, v_x_2207__boxed_4943_, v_x_2208__boxed_4944_, v_x_4941_, v_x_4942_);
    return v_res_4945_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4946_: *mut leanh::LeanObject,
    mut v_keys_4947_: *mut leanh::LeanObject,
    mut v_vals_4948_: *mut leanh::LeanObject,
    mut v_heq_4949_: *mut leanh::LeanObject,
    mut v_i_4950_: *mut leanh::LeanObject,
    mut v_k_4951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4952_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_4947_, v_vals_4948_, v_i_4950_, v_k_4951_);
    return v___x_4952_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4953_: *mut leanh::LeanObject,
    mut v_keys_4954_: *mut leanh::LeanObject,
    mut v_vals_4955_: *mut leanh::LeanObject,
    mut v_heq_4956_: *mut leanh::LeanObject,
    mut v_i_4957_: *mut leanh::LeanObject,
    mut v_k_4958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4959_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4953_, v_keys_4954_, v_vals_4955_, v_heq_4956_, v_i_4957_, v_k_4958_);
    leanh::lean_dec(v_k_4958_);
    leanh::lean_dec_ref(v_vals_4955_);
    leanh::lean_dec_ref(v_keys_4954_);
    return v_res_4959_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4960_: *mut leanh::LeanObject,
    mut v_n_4961_: *mut leanh::LeanObject,
    mut v_k_4962_: *mut leanh::LeanObject,
    mut v_v_4963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4964_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v_n_4961_, v_k_4962_, v_v_4963_);
    return v___x_4964_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_4965_: *mut leanh::LeanObject,
    mut v_depth_4966_: usize,
    mut v_keys_4967_: *mut leanh::LeanObject,
    mut v_vals_4968_: *mut leanh::LeanObject,
    mut v_heq_4969_: *mut leanh::LeanObject,
    mut v_i_4970_: *mut leanh::LeanObject,
    mut v_entries_4971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4972_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_4966_, v_keys_4967_, v_vals_4968_, v_i_4970_, v_entries_4971_);
    return v___x_4972_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_4973_: *mut leanh::LeanObject,
    mut v_depth_4974_: *mut leanh::LeanObject,
    mut v_keys_4975_: *mut leanh::LeanObject,
    mut v_vals_4976_: *mut leanh::LeanObject,
    mut v_heq_4977_: *mut leanh::LeanObject,
    mut v_i_4978_: *mut leanh::LeanObject,
    mut v_entries_4979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4980_ = leanh::lean_unbox_usize(v_depth_4974_);
    leanh::lean_dec(v_depth_4974_);
    v_res_4981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_4973_, v_depth_boxed_4980_, v_keys_4975_, v_vals_4976_, v_heq_4977_, v_i_4978_, v_entries_4979_);
    leanh::lean_dec_ref(v_vals_4976_);
    leanh::lean_dec_ref(v_keys_4975_);
    return v_res_4981_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(
    mut v_x_4982_: *mut leanh::LeanObject,
    mut v_keys_4983_: *mut leanh::LeanObject,
    mut v_v_4984_: *mut leanh::LeanObject,
    mut v_k_4985_: *mut leanh::LeanObject,
    mut v_as_4986_: *mut leanh::LeanObject,
    mut v_k_4987_: *mut leanh::LeanObject,
    mut v_x_4988_: *mut leanh::LeanObject,
    mut v_x_4989_: *mut leanh::LeanObject,
    mut v_x_4990_: *mut leanh::LeanObject,
    mut v_x_4991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4992_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_4982_, v_keys_4983_, v_v_4984_, v_k_4985_, v_as_4986_, v_k_4987_, v_x_4988_, v_x_4989_);
    return v___x_4992_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_x_4993_: *mut leanh::LeanObject,
    mut v_keys_4994_: *mut leanh::LeanObject,
    mut v_v_4995_: *mut leanh::LeanObject,
    mut v_k_4996_: *mut leanh::LeanObject,
    mut v_as_4997_: *mut leanh::LeanObject,
    mut v_k_4998_: *mut leanh::LeanObject,
    mut v_x_4999_: *mut leanh::LeanObject,
    mut v_x_5000_: *mut leanh::LeanObject,
    mut v_x_5001_: *mut leanh::LeanObject,
    mut v_x_5002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5003_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(v_x_4993_, v_keys_4994_, v_v_4995_, v_k_4996_, v_as_4997_, v_k_4998_, v_x_4999_, v_x_5000_, v_x_5001_, v_x_5002_);
    leanh::lean_dec_ref(v_k_4998_);
    leanh::lean_dec_ref(v_keys_4994_);
    leanh::lean_dec(v_x_4993_);
    return v_res_5003_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_5004_: *mut leanh::LeanObject,
    mut v_x_5005_: *mut leanh::LeanObject,
    mut v_x_5006_: *mut leanh::LeanObject,
    mut v_x_5007_: *mut leanh::LeanObject,
    mut v_x_5008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5009_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_5005_, v_x_5006_, v_x_5007_, v_x_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(
    mut v_keys_5010_: *mut leanh::LeanObject,
    mut v_i_5011_: *mut leanh::LeanObject,
    mut v_k_5012_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: u8 = 0;
    let mut v_k_x27_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5013_ = lean_array_get_size(v_keys_5010_);
                v___x_5014_ = lean_nat_dec_lt(v_i_5011_, v___x_5013_);
                if v___x_5014_ == 0 {
                    leanh::lean_dec_ref(v_k_5012_);
                    leanh::lean_dec(v_i_5011_);
                    return v___x_5014_;
                } else {
                    v_k_x27_5015_ = lean_array_fget_borrowed(v_keys_5010_, v_i_5011_);
                    leanh::lean_inc(v_k_x27_5015_);
                    leanh::lean_inc_ref(v_k_5012_);
                    v___x_5016_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_k_5012_,
                        v_k_x27_5015_,
                    );
                    if v___x_5016_ == 0 {
                        v___x_5017_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5018_ = lean_nat_add(v_i_5011_, v___x_5017_);
                        leanh::lean_dec(v_i_5011_);
                        v_i_5011_ = v___x_5018_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_5012_);
                        leanh::lean_dec(v_i_5011_);
                        return v___x_5016_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_5020_: *mut leanh::LeanObject,
    mut v_i_5021_: *mut leanh::LeanObject,
    mut v_k_5022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5023_: u8 = 0;
    let mut v_r_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5023_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_5020_, v_i_5021_, v_k_5022_);
    leanh::lean_dec_ref(v_keys_5020_);
    v_r_5024_ = leanh::lean_box((v_res_5023_) as usize);
    return v_r_5024_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(
    mut v_x_5025_: *mut leanh::LeanObject,
    mut v_x_5026_: usize,
    mut v_x_5027_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: usize = 0;
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: usize = 0;
    let mut v_j_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v_node_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: usize = 0;
    let mut v___x_5040_: u8 = 0;
    let mut v_ks_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5025_) == 0 {
                    v_es_5028_ = leanh::lean_ctor_get(v_x_5025_, 0);
                    leanh::lean_inc_ref(v_es_5028_);
                    leanh::lean_dec_ref_known(v_x_5025_, 1);
                    v___x_5029_ = leanh::lean_box(2);
                    v___x_5030_ = 5usize;
                    v___x_5031_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_5032_ = lean_usize_land(v_x_5026_, v___x_5031_);
                    v_j_5033_ = lean_usize_to_nat(v___x_5032_);
                    v___x_5034_ = lean_array_get(v___x_5029_, v_es_5028_, v_j_5033_);
                    leanh::lean_dec(v_j_5033_);
                    leanh::lean_dec_ref(v_es_5028_);
                    match leanh::lean_obj_tag(v___x_5034_) {
                        0 => {
                            v_key_5035_ = leanh::lean_ctor_get(v___x_5034_, 0);
                            leanh::lean_inc(v_key_5035_);
                            leanh::lean_dec_ref_known(v___x_5034_, 2);
                            v___x_5036_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                                v_x_5027_,
                                v_key_5035_,
                            );
                            return v___x_5036_;
                        }
                        1 => {
                            v_node_5037_ = leanh::lean_ctor_get(v___x_5034_, 0);
                            leanh::lean_inc(v_node_5037_);
                            leanh::lean_dec_ref_known(v___x_5034_, 1);
                            v___x_5038_ = lean_usize_shift_right(v_x_5026_, v___x_5030_);
                            v_x_5025_ = v_node_5037_;
                            v_x_5026_ = v___x_5038_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_x_5027_);
                            v___x_5040_ = 0;
                            return v___x_5040_;
                        }
                    }
                } else {
                    v_ks_5041_ = leanh::lean_ctor_get(v_x_5025_, 0);
                    leanh::lean_inc_ref(v_ks_5041_);
                    leanh::lean_dec_ref_known(v_x_5025_, 2);
                    v___x_5042_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_ks_5041_, v___x_5042_, v_x_5027_);
                    leanh::lean_dec_ref(v_ks_5041_);
                    return v___x_5043_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(
    mut v_x_5044_: *mut leanh::LeanObject,
    mut v_x_5045_: *mut leanh::LeanObject,
    mut v_x_5046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_146__boxed_5047_: usize = 0;
    let mut v_res_5048_: u8 = 0;
    let mut v_r_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_146__boxed_5047_ = leanh::lean_unbox_usize(v_x_5045_);
    leanh::lean_dec(v_x_5045_);
    v_res_5048_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_5044_, v_x_146__boxed_5047_, v_x_5046_);
    v_r_5049_ = leanh::lean_box((v_res_5048_) as usize);
    return v_r_5049_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(
    mut v_x_5050_: *mut leanh::LeanObject,
    mut v_x_5051_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_5053_: u64 = 0;
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: u8 = 0;
    let mut v___y_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u64 = 0;
    let mut v_hash_5059_: u64 = 0;
    let mut v_declName_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_5060_ = leanh::lean_ctor_get(v_x_5051_, 0);
                leanh::lean_inc(v_declName_5060_);
                v___y_5057_ = v_declName_5060_;
                state = 2;
                continue;
            }
            1 => {
                v___x_5054_ = lean_uint64_to_usize(v___y_5053_);
                v___x_5055_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_5050_, v___x_5054_, v_x_5051_);
                return v___x_5055_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_5057_) == 0 {
                    v___x_5058_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    v___y_5053_ = v___x_5058_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5059_ = leanh::lean_ctor_get_uint64(
                        v___y_5057_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___y_5057_);
                    v___y_5053_ = v_hash_5059_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg___boxed(
    mut v_x_5061_: *mut leanh::LeanObject,
    mut v_x_5062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5063_: u8 = 0;
    let mut v_r_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_5061_, v_x_5062_);
    v_r_5064_ = leanh::lean_box((v_res_5063_) as usize);
    return v_r_5064_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(
    mut v_d_5065_: *mut leanh::LeanObject,
    mut v_thmId_5066_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_erased_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: u8 = 0;
    v_erased_5067_ = leanh::lean_ctor_get(v_d_5065_, 1);
    leanh::lean_inc_ref(v_erased_5067_);
    leanh::lean_dec_ref(v_d_5065_);
    v___x_5068_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_erased_5067_, v_thmId_5066_);
    return v___x_5068_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased___boxed(
    mut v_d_5069_: *mut leanh::LeanObject,
    mut v_thmId_5070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5071_: u8 = 0;
    let mut v_r_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5071_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_d_5069_, v_thmId_5070_);
    v_r_5072_ = leanh::lean_box((v_res_5071_) as usize);
    return v_r_5072_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(
    mut v_00_u03b2_5073_: *mut leanh::LeanObject,
    mut v_x_5074_: *mut leanh::LeanObject,
    mut v_x_5075_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5076_: u8 = 0;
    v___x_5076_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_5074_, v_x_5075_);
    return v___x_5076_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___boxed(
    mut v_00_u03b2_5077_: *mut leanh::LeanObject,
    mut v_x_5078_: *mut leanh::LeanObject,
    mut v_x_5079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5080_: u8 = 0;
    let mut v_r_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5080_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(v_00_u03b2_5077_, v_x_5078_, v_x_5079_);
    v_r_5081_ = leanh::lean_box((v_res_5080_) as usize);
    return v_r_5081_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(
    mut v_00_u03b2_5082_: *mut leanh::LeanObject,
    mut v_x_5083_: *mut leanh::LeanObject,
    mut v_x_5084_: usize,
    mut v_x_5085_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5086_: u8 = 0;
    v___x_5086_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_5083_, v_x_5084_, v_x_5085_);
    return v___x_5086_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(
    mut v_00_u03b2_5087_: *mut leanh::LeanObject,
    mut v_x_5088_: *mut leanh::LeanObject,
    mut v_x_5089_: *mut leanh::LeanObject,
    mut v_x_5090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_228__boxed_5091_: usize = 0;
    let mut v_res_5092_: u8 = 0;
    let mut v_r_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_228__boxed_5091_ = leanh::lean_unbox_usize(v_x_5089_);
    leanh::lean_dec(v_x_5089_);
    v_res_5092_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(v_00_u03b2_5087_, v_x_5088_, v_x_228__boxed_5091_, v_x_5090_);
    v_r_5093_ = leanh::lean_box((v_res_5092_) as usize);
    return v_r_5093_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5094_: *mut leanh::LeanObject,
    mut v_keys_5095_: *mut leanh::LeanObject,
    mut v_vals_5096_: *mut leanh::LeanObject,
    mut v_heq_5097_: *mut leanh::LeanObject,
    mut v_i_5098_: *mut leanh::LeanObject,
    mut v_k_5099_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5100_: u8 = 0;
    v___x_5100_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_5095_, v_i_5098_, v_k_5099_);
    return v___x_5100_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5101_: *mut leanh::LeanObject,
    mut v_keys_5102_: *mut leanh::LeanObject,
    mut v_vals_5103_: *mut leanh::LeanObject,
    mut v_heq_5104_: *mut leanh::LeanObject,
    mut v_i_5105_: *mut leanh::LeanObject,
    mut v_k_5106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5107_: u8 = 0;
    let mut v_r_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5107_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(v_00_u03b2_5101_, v_keys_5102_, v_vals_5103_, v_heq_5104_, v_i_5105_, v_k_5106_);
    leanh::lean_dec_ref(v_vals_5103_);
    leanh::lean_dec_ref(v_keys_5102_);
    v_r_5108_ = leanh::lean_box((v_res_5107_) as usize);
    return v_r_5108_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_5109_: *mut leanh::LeanObject,
    mut v_x_5110_: *mut leanh::LeanObject,
    mut v_x_5111_: *mut leanh::LeanObject,
    mut v_x_5112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5117_: u8 = 0;
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5113_ = leanh::lean_ctor_get(v_x_5109_, 0);
                v_vs_5114_ = leanh::lean_ctor_get(v_x_5109_, 1);
                v_isSharedCheck_5138_ = (!leanh::lean_is_exclusive(v_x_5109_)) as u8;
                if v_isSharedCheck_5138_ == 0 {
                    v___x_5116_ = v_x_5109_;
                    v_isShared_5117_ = v_isSharedCheck_5138_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_5114_);
                    leanh::lean_inc(v_ks_5113_);
                    leanh::lean_dec(v_x_5109_);
                    v___x_5116_ = leanh::lean_box(0);
                    v_isShared_5117_ = v_isSharedCheck_5138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5118_ = lean_array_get_size(v_ks_5113_);
                v___x_5119_ = lean_nat_dec_lt(v_x_5110_, v___x_5118_);
                if v___x_5119_ == 0 {
                    leanh::lean_dec(v_x_5110_);
                    v___x_5120_ = lean_array_push(v_ks_5113_, v_x_5111_);
                    v___x_5121_ = lean_array_push(v_vs_5114_, v_x_5112_);
                    if v_isShared_5117_ == 0 {
                        leanh::lean_ctor_set(v___x_5116_, 1, v___x_5121_);
                        leanh::lean_ctor_set(v___x_5116_, 0, v___x_5120_);
                        v___x_5123_ = v___x_5116_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5124_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v___x_5120_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 1, v___x_5121_);
                        v___x_5123_ = v_reuseFailAlloc_5124_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5125_ = lean_array_fget_borrowed(v_ks_5113_, v_x_5110_);
                    leanh::lean_inc(v_k_x27_5125_);
                    leanh::lean_inc_ref(v_x_5111_);
                    v___x_5126_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_x_5111_,
                        v_k_x27_5125_,
                    );
                    if v___x_5126_ == 0 {
                        if v_isShared_5117_ == 0 {
                            v___x_5128_ = v___x_5116_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5132_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_ks_5113_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_vs_5114_);
                            v___x_5128_ = v_reuseFailAlloc_5132_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5133_ = lean_array_fset(v_ks_5113_, v_x_5110_, v_x_5111_);
                        v___x_5134_ = lean_array_fset(v_vs_5114_, v_x_5110_, v_x_5112_);
                        leanh::lean_dec(v_x_5110_);
                        if v_isShared_5117_ == 0 {
                            leanh::lean_ctor_set(v___x_5116_, 1, v___x_5134_);
                            leanh::lean_ctor_set(v___x_5116_, 0, v___x_5133_);
                            v___x_5136_ = v___x_5116_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5137_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5133_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 1, v___x_5134_);
                            v___x_5136_ = v_reuseFailAlloc_5137_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5123_;
            }
            3 => {
                v___x_5129_ = leanh::lean_unsigned_to_nat(1);
                v___x_5130_ = lean_nat_add(v_x_5110_, v___x_5129_);
                leanh::lean_dec(v_x_5110_);
                v_x_5109_ = v___x_5128_;
                v_x_5110_ = v___x_5130_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(
    mut v_n_5139_: *mut leanh::LeanObject,
    mut v_k_5140_: *mut leanh::LeanObject,
    mut v_v_5141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5142_ = leanh::lean_unsigned_to_nat(0);
    v___x_5143_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_n_5139_, v___x_5142_, v_k_5140_, v_v_5141_);
    return v___x_5143_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5144_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5144_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(
    mut v_x_5145_: *mut leanh::LeanObject,
    mut v_x_5146_: usize,
    mut v_x_5147_: usize,
    mut v_x_5148_: *mut leanh::LeanObject,
    mut v_x_5149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: usize = 0;
    let mut v___x_5152_: usize = 0;
    let mut v___x_5153_: usize = 0;
    let mut v___x_5154_: usize = 0;
    let mut v_j_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: u8 = 0;
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v_v_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5174_: u8 = 0;
    let mut v___x_5175_: u8 = 0;
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut v_node_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5185_: u8 = 0;
    let mut v___x_5186_: usize = 0;
    let mut v___x_5187_: usize = 0;
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v_unused_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5200_: u8 = 0;
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5205_: u8 = 0;
    let mut v_ks_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: u8 = 0;
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: u8 = 0;
    let mut v_reuseFailAlloc_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5145_) == 0 {
                    v_es_5150_ = leanh::lean_ctor_get(v_x_5145_, 0);
                    v___x_5151_ = 5usize;
                    v___x_5152_ = 1usize;
                    v___x_5153_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_5154_ = lean_usize_land(v_x_5146_, v___x_5153_);
                    v_j_5155_ = lean_usize_to_nat(v___x_5154_);
                    v___x_5156_ = lean_array_get_size(v_es_5150_);
                    v___x_5157_ = lean_nat_dec_lt(v_j_5155_, v___x_5156_);
                    if v___x_5157_ == 0 {
                        leanh::lean_dec(v_j_5155_);
                        leanh::lean_dec(v_x_5149_);
                        leanh::lean_dec_ref(v_x_5148_);
                        return v_x_5145_;
                    } else {
                        leanh::lean_inc_ref(v_es_5150_);
                        v_isSharedCheck_5194_ = (!leanh::lean_is_exclusive(v_x_5145_)) as u8;
                        if v_isSharedCheck_5194_ == 0 {
                            v_unused_5195_ = leanh::lean_ctor_get(v_x_5145_, 0);
                            leanh::lean_dec(v_unused_5195_);
                            v___x_5159_ = v_x_5145_;
                            v_isShared_5160_ = v_isSharedCheck_5194_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_5145_);
                            v___x_5159_ = leanh::lean_box(0);
                            v_isShared_5160_ = v_isSharedCheck_5194_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5196_ = leanh::lean_ctor_get(v_x_5145_, 0);
                    v_vs_5197_ = leanh::lean_ctor_get(v_x_5145_, 1);
                    v_isSharedCheck_5217_ = (!leanh::lean_is_exclusive(v_x_5145_)) as u8;
                    if v_isSharedCheck_5217_ == 0 {
                        v___x_5199_ = v_x_5145_;
                        v_isShared_5200_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5197_);
                        leanh::lean_inc(v_ks_5196_);
                        leanh::lean_dec(v_x_5145_);
                        v___x_5199_ = leanh::lean_box(0);
                        v_isShared_5200_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5161_ = lean_array_fget(v_es_5150_, v_j_5155_);
                v___x_5162_ = leanh::lean_box(0);
                v_xs_x27_5163_ = lean_array_fset(v_es_5150_, v_j_5155_, v___x_5162_);
                match leanh::lean_obj_tag(v_v_5161_) {
                    0 => {
                        v_key_5170_ = leanh::lean_ctor_get(v_v_5161_, 0);
                        v_val_5171_ = leanh::lean_ctor_get(v_v_5161_, 1);
                        v_isSharedCheck_5181_ = (!leanh::lean_is_exclusive(v_v_5161_)) as u8;
                        if v_isSharedCheck_5181_ == 0 {
                            v___x_5173_ = v_v_5161_;
                            v_isShared_5174_ = v_isSharedCheck_5181_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5171_);
                            leanh::lean_inc(v_key_5170_);
                            leanh::lean_dec(v_v_5161_);
                            v___x_5173_ = leanh::lean_box(0);
                            v_isShared_5174_ = v_isSharedCheck_5181_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5182_ = leanh::lean_ctor_get(v_v_5161_, 0);
                        v_isSharedCheck_5192_ = (!leanh::lean_is_exclusive(v_v_5161_)) as u8;
                        if v_isSharedCheck_5192_ == 0 {
                            v___x_5184_ = v_v_5161_;
                            v_isShared_5185_ = v_isSharedCheck_5192_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_5182_);
                            leanh::lean_dec(v_v_5161_);
                            v___x_5184_ = leanh::lean_box(0);
                            v_isShared_5185_ = v_isSharedCheck_5192_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5193_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5193_, 0, v_x_5148_);
                        leanh::lean_ctor_set(v___x_5193_, 1, v_x_5149_);
                        v___y_5165_ = v___x_5193_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5166_ = lean_array_fset(v_xs_x27_5163_, v_j_5155_, v___y_5165_);
                leanh::lean_dec(v_j_5155_);
                if v_isShared_5160_ == 0 {
                    leanh::lean_ctor_set(v___x_5159_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5159_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5168_;
            }
            4 => {
                leanh::lean_inc(v_key_5170_);
                leanh::lean_inc_ref(v_x_5148_);
                v___x_5175_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_5148_, v_key_5170_);
                if v___x_5175_ == 0 {
                    leanh::lean_del_object(v___x_5173_);
                    v___x_5176_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5170_,
                        v_val_5171_,
                        v_x_5148_,
                        v_x_5149_,
                    );
                    v___x_5177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5177_, 0, v___x_5176_);
                    v___y_5165_ = v___x_5177_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_5171_);
                    leanh::lean_dec(v_key_5170_);
                    if v_isShared_5174_ == 0 {
                        leanh::lean_ctor_set(v___x_5173_, 1, v_x_5149_);
                        leanh::lean_ctor_set(v___x_5173_, 0, v_x_5148_);
                        v___x_5179_ = v___x_5173_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5180_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_x_5148_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_x_5149_);
                        v___x_5179_ = v_reuseFailAlloc_5180_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5165_ = v___x_5179_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5186_ = lean_usize_shift_right(v_x_5146_, v___x_5151_);
                v___x_5187_ = lean_usize_add(v_x_5147_, v___x_5152_);
                v___x_5188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_node_5182_, v___x_5186_, v___x_5187_, v_x_5148_, v_x_5149_);
                if v_isShared_5185_ == 0 {
                    leanh::lean_ctor_set(v___x_5184_, 0, v___x_5188_);
                    v___x_5190_ = v___x_5184_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5188_);
                    v___x_5190_ = v_reuseFailAlloc_5191_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5165_ = v___x_5190_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5200_ == 0 {
                    v___x_5202_ = v___x_5199_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5216_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_ks_5196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 1, v_vs_5197_);
                    v___x_5202_ = v_reuseFailAlloc_5216_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5203_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v___x_5202_, v_x_5148_, v_x_5149_);
                v___x_5211_ = 7usize;
                v___x_5212_ = lean_usize_dec_le(v___x_5211_, v_x_5147_);
                if v___x_5212_ == 0 {
                    v___x_5213_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5203_);
                    v___x_5214_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5215_ = lean_nat_dec_lt(v___x_5213_, v___x_5214_);
                    leanh::lean_dec(v___x_5213_);
                    v___y_5205_ = v___x_5215_;
                    state = 10;
                    continue;
                } else {
                    v___y_5205_ = v___x_5212_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5205_ == 0 {
                    v_ks_5206_ = leanh::lean_ctor_get(v_newNode_5203_, 0);
                    leanh::lean_inc_ref(v_ks_5206_);
                    v_vs_5207_ = leanh::lean_ctor_get(v_newNode_5203_, 1);
                    leanh::lean_inc_ref(v_vs_5207_);
                    leanh::lean_dec_ref(v_newNode_5203_);
                    v___x_5208_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5209_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0);
                    v___x_5210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_x_5147_, v_ks_5206_, v_vs_5207_, v___x_5208_, v___x_5209_);
                    leanh::lean_dec_ref(v_vs_5207_);
                    leanh::lean_dec_ref(v_ks_5206_);
                    return v___x_5210_;
                } else {
                    return v_newNode_5203_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(
    mut v_depth_5218_: usize,
    mut v_keys_5219_: *mut leanh::LeanObject,
    mut v_vals_5220_: *mut leanh::LeanObject,
    mut v_i_5221_: *mut leanh::LeanObject,
    mut v_entries_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    let mut v_k_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5228_: u64 = 0;
    let mut v_h_5229_: usize = 0;
    let mut v___x_5230_: usize = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: usize = 0;
    let mut v___x_5233_: usize = 0;
    let mut v___x_5234_: usize = 0;
    let mut v_h_5235_: usize = 0;
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u64 = 0;
    let mut v_hash_5242_: u64 = 0;
    let mut v_declName_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = lean_array_get_size(v_keys_5219_);
                v___x_5224_ = lean_nat_dec_lt(v_i_5221_, v___x_5223_);
                if v___x_5224_ == 0 {
                    leanh::lean_dec(v_i_5221_);
                    return v_entries_5222_;
                } else {
                    v_k_5225_ = lean_array_fget_borrowed(v_keys_5219_, v_i_5221_);
                    v_v_5226_ = lean_array_fget_borrowed(v_vals_5220_, v_i_5221_);
                    v_declName_5243_ = leanh::lean_ctor_get(v_k_5225_, 0);
                    leanh::lean_inc(v_declName_5243_);
                    v___y_5240_ = v_declName_5243_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_h_5229_ = lean_uint64_to_usize(v___y_5228_);
                v___x_5230_ = 5usize;
                v___x_5231_ = leanh::lean_unsigned_to_nat(1);
                v___x_5232_ = 1usize;
                v___x_5233_ = lean_usize_sub(v_depth_5218_, v___x_5232_);
                v___x_5234_ = lean_usize_mul(v___x_5230_, v___x_5233_);
                v_h_5235_ = lean_usize_shift_right(v_h_5229_, v___x_5234_);
                v___x_5236_ = lean_nat_add(v_i_5221_, v___x_5231_);
                leanh::lean_dec(v_i_5221_);
                leanh::lean_inc(v_v_5226_);
                leanh::lean_inc(v_k_5225_);
                v___x_5237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_entries_5222_, v_h_5235_, v_depth_5218_, v_k_5225_, v_v_5226_);
                v_i_5221_ = v___x_5236_;
                v_entries_5222_ = v___x_5237_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_5240_) == 0 {
                    v___x_5241_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    v___y_5228_ = v___x_5241_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5242_ = leanh::lean_ctor_get_uint64(
                        v___y_5240_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___y_5240_);
                    v___y_5228_ = v_hash_5242_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_5244_: *mut leanh::LeanObject,
    mut v_keys_5245_: *mut leanh::LeanObject,
    mut v_vals_5246_: *mut leanh::LeanObject,
    mut v_i_5247_: *mut leanh::LeanObject,
    mut v_entries_5248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5249_: usize = 0;
    let mut v_res_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5249_ = leanh::lean_unbox_usize(v_depth_5244_);
    leanh::lean_dec(v_depth_5244_);
    v_res_5250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_5249_, v_keys_5245_, v_vals_5246_, v_i_5247_, v_entries_5248_);
    leanh::lean_dec_ref(v_vals_5246_);
    leanh::lean_dec_ref(v_keys_5245_);
    return v_res_5250_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(
    mut v_x_5251_: *mut leanh::LeanObject,
    mut v_x_5252_: *mut leanh::LeanObject,
    mut v_x_5253_: *mut leanh::LeanObject,
    mut v_x_5254_: *mut leanh::LeanObject,
    mut v_x_5255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_400__boxed_5256_: usize = 0;
    let mut v_x_401__boxed_5257_: usize = 0;
    let mut v_res_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_400__boxed_5256_ = leanh::lean_unbox_usize(v_x_5252_);
    leanh::lean_dec(v_x_5252_);
    v_x_401__boxed_5257_ = leanh::lean_unbox_usize(v_x_5253_);
    leanh::lean_dec(v_x_5253_);
    v_res_5258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_5251_, v_x_400__boxed_5256_, v_x_401__boxed_5257_, v_x_5254_, v_x_5255_);
    return v_res_5258_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(
    mut v_x_5259_: *mut leanh::LeanObject,
    mut v_x_5260_: *mut leanh::LeanObject,
    mut v_x_5261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5263_: u64 = 0;
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: usize = 0;
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u64 = 0;
    let mut v_hash_5270_: u64 = 0;
    let mut v_declName_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_5271_ = leanh::lean_ctor_get(v_x_5260_, 0);
                leanh::lean_inc(v_declName_5271_);
                v___y_5268_ = v_declName_5271_;
                state = 2;
                continue;
            }
            1 => {
                v___x_5264_ = lean_uint64_to_usize(v___y_5263_);
                v___x_5265_ = 1usize;
                v___x_5266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_5259_, v___x_5264_, v___x_5265_, v_x_5260_, v_x_5261_);
                return v___x_5266_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_5268_) == 0 {
                    v___x_5269_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    v___y_5263_ = v___x_5269_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5270_ = leanh::lean_ctor_get_uint64(
                        v___y_5268_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___y_5268_);
                    v___y_5263_ = v_hash_5270_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(
    mut v_d_5272_: *mut leanh::LeanObject,
    mut v_thmId_5273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_specs_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_5274_ = leanh::lean_ctor_get(v_d_5272_, 0);
                v_erased_5275_ = leanh::lean_ctor_get(v_d_5272_, 1);
                v_isSharedCheck_5284_ = (!leanh::lean_is_exclusive(v_d_5272_)) as u8;
                if v_isSharedCheck_5284_ == 0 {
                    v___x_5277_ = v_d_5272_;
                    v_isShared_5278_ = v_isSharedCheck_5284_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_5275_);
                    leanh::lean_inc(v_specs_5274_);
                    leanh::lean_dec(v_d_5272_);
                    v___x_5277_ = leanh::lean_box(0);
                    v_isShared_5278_ = v_isSharedCheck_5284_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5279_ = leanh::lean_box(0);
                v___x_5280_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_erased_5275_, v_thmId_5273_, v___x_5279_);
                if v_isShared_5278_ == 0 {
                    leanh::lean_ctor_set(v___x_5277_, 1, v___x_5280_);
                    v___x_5282_ = v___x_5277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_specs_5274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___x_5280_);
                    v___x_5282_ = v_reuseFailAlloc_5283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0(
    mut v_00_u03b2_5285_: *mut leanh::LeanObject,
    mut v_x_5286_: *mut leanh::LeanObject,
    mut v_x_5287_: *mut leanh::LeanObject,
    mut v_x_5288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5289_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_x_5286_, v_x_5287_, v_x_5288_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(
    mut v_00_u03b2_5290_: *mut leanh::LeanObject,
    mut v_x_5291_: *mut leanh::LeanObject,
    mut v_x_5292_: usize,
    mut v_x_5293_: usize,
    mut v_x_5294_: *mut leanh::LeanObject,
    mut v_x_5295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_5291_, v_x_5292_, v_x_5293_, v_x_5294_, v_x_5295_);
    return v___x_5296_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(
    mut v_00_u03b2_5297_: *mut leanh::LeanObject,
    mut v_x_5298_: *mut leanh::LeanObject,
    mut v_x_5299_: *mut leanh::LeanObject,
    mut v_x_5300_: *mut leanh::LeanObject,
    mut v_x_5301_: *mut leanh::LeanObject,
    mut v_x_5302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_618__boxed_5303_: usize = 0;
    let mut v_x_619__boxed_5304_: usize = 0;
    let mut v_res_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_618__boxed_5303_ = leanh::lean_unbox_usize(v_x_5299_);
    leanh::lean_dec(v_x_5299_);
    v_x_619__boxed_5304_ = leanh::lean_unbox_usize(v_x_5300_);
    leanh::lean_dec(v_x_5300_);
    v_res_5305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(v_00_u03b2_5297_, v_x_5298_, v_x_618__boxed_5303_, v_x_619__boxed_5304_, v_x_5301_, v_x_5302_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5306_: *mut leanh::LeanObject,
    mut v_n_5307_: *mut leanh::LeanObject,
    mut v_k_5308_: *mut leanh::LeanObject,
    mut v_v_5309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v_n_5307_, v_k_5308_, v_v_5309_);
    return v___x_5310_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5311_: *mut leanh::LeanObject,
    mut v_depth_5312_: usize,
    mut v_keys_5313_: *mut leanh::LeanObject,
    mut v_vals_5314_: *mut leanh::LeanObject,
    mut v_heq_5315_: *mut leanh::LeanObject,
    mut v_i_5316_: *mut leanh::LeanObject,
    mut v_entries_5317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_5312_, v_keys_5313_, v_vals_5314_, v_i_5316_, v_entries_5317_);
    return v___x_5318_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5319_: *mut leanh::LeanObject,
    mut v_depth_5320_: *mut leanh::LeanObject,
    mut v_keys_5321_: *mut leanh::LeanObject,
    mut v_vals_5322_: *mut leanh::LeanObject,
    mut v_heq_5323_: *mut leanh::LeanObject,
    mut v_i_5324_: *mut leanh::LeanObject,
    mut v_entries_5325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5326_: usize = 0;
    let mut v_res_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5326_ = leanh::lean_unbox_usize(v_depth_5320_);
    leanh::lean_dec(v_depth_5320_);
    v_res_5327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(v_00_u03b2_5319_, v_depth_boxed_5326_, v_keys_5321_, v_vals_5322_, v_heq_5323_, v_i_5324_, v_entries_5325_);
    leanh::lean_dec_ref(v_vals_5322_);
    leanh::lean_dec_ref(v_keys_5321_);
    return v_res_5327_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5328_: *mut leanh::LeanObject,
    mut v_x_5329_: *mut leanh::LeanObject,
    mut v_x_5330_: *mut leanh::LeanObject,
    mut v_x_5331_: *mut leanh::LeanObject,
    mut v_x_5332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5333_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_x_5329_, v_x_5330_, v_x_5331_, v_x_5332_);
    return v___x_5333_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(
    mut v_a_5334_: *mut leanh::LeanObject,
    mut v_as_5335_: *mut leanh::LeanObject,
    mut v_i_5336_: usize,
    mut v_stop_5337_: usize,
) -> u8 {
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: u8 = 0;
    let mut v___x_5341_: usize = 0;
    let mut v___x_5342_: usize = 0;
    let mut v___x_5344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5338_ = lean_usize_dec_eq(v_i_5336_, v_stop_5337_);
                if v___x_5338_ == 0 {
                    v___x_5339_ = lean_array_uget_borrowed(v_as_5335_, v_i_5336_);
                    v___x_5340_ = lean_expr_eqv(v_a_5334_, v___x_5339_);
                    if v___x_5340_ == 0 {
                        v___x_5341_ = 1usize;
                        v___x_5342_ = lean_usize_add(v_i_5336_, v___x_5341_);
                        v_i_5336_ = v___x_5342_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5340_;
                    }
                } else {
                    v___x_5344_ = 0;
                    return v___x_5344_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0___boxed(
    mut v_a_5345_: *mut leanh::LeanObject,
    mut v_as_5346_: *mut leanh::LeanObject,
    mut v_i_5347_: *mut leanh::LeanObject,
    mut v_stop_5348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5349_: usize = 0;
    let mut v_stop_boxed_5350_: usize = 0;
    let mut v_res_5351_: u8 = 0;
    let mut v_r_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5349_ = leanh::lean_unbox_usize(v_i_5347_);
    leanh::lean_dec(v_i_5347_);
    v_stop_boxed_5350_ = leanh::lean_unbox_usize(v_stop_5348_);
    leanh::lean_dec(v_stop_5348_);
    v_res_5351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_5345_, v_as_5346_, v_i_boxed_5349_, v_stop_boxed_5350_);
    leanh::lean_dec_ref(v_as_5346_);
    leanh::lean_dec_ref(v_a_5345_);
    v_r_5352_ = leanh::lean_box((v_res_5351_) as usize);
    return v_r_5352_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(
    mut v_as_5353_: *mut leanh::LeanObject,
    mut v_a_5354_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: u8 = 0;
    v___x_5355_ = leanh::lean_unsigned_to_nat(0);
    v___x_5356_ = lean_array_get_size(v_as_5353_);
    v___x_5357_ = lean_nat_dec_lt(v___x_5355_, v___x_5356_);
    if v___x_5357_ == 0 {
        return v___x_5357_;
    } else {
        if v___x_5357_ == 0 {
            return v___x_5357_;
        } else {
            let mut v___x_5358_: usize = 0;
            let mut v___x_5359_: usize = 0;
            let mut v___x_5360_: u8 = 0;
            v___x_5358_ = 0usize;
            v___x_5359_ = lean_usize_of_nat(v___x_5356_);
            v___x_5360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_5354_, v_as_5353_, v___x_5358_, v___x_5359_);
            return v___x_5360_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0___boxed(
    mut v_as_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5363_: u8 = 0;
    let mut v_r_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5363_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_as_5361_, v_a_5362_);
    leanh::lean_dec_ref(v_a_5362_);
    leanh::lean_dec_ref(v_as_5361_);
    v_r_5364_ = leanh::lean_box((v_res_5363_) as usize);
    return v_r_5364_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(
    mut v_xs_5368_: *mut leanh::LeanObject,
    mut v_e_5369_: *mut leanh::LeanObject,
    mut v_a_5370_: *mut leanh::LeanObject,
    mut v_a_5371_: *mut leanh::LeanObject,
    mut v_a_5372_: *mut leanh::LeanObject,
    mut v_a_5373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ty_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5429_: u8 = 0;
    let mut v_l_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: u8 = 0;
    let mut v___x_5434_: u8 = 0;
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: u8 = 0;
    let mut v___y_5441_: u8 = 0;
    let mut v___x_5442_: u8 = 0;
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: u8 = 0;
    let mut v___x_5446_: u8 = 0;
    let mut v_binderType_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5462_: u8 = 0;
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v_expr_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5394_ = l_Lean_Expr_hasExprMVar(v_e_5369_);
                if v___x_5394_ == 0 {
                    v___x_5395_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5396_, 0, v___x_5395_);
                    return v___x_5396_;
                } else {
                    match leanh::lean_obj_tag(v_e_5369_) {
                        5 => {
                            v_fn_5397_ = leanh::lean_ctor_get(v_e_5369_, 0);
                            v_arg_5398_ = leanh::lean_ctor_get(v_e_5369_, 1);
                            v___x_5399_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1;
                            v___x_5400_ = leanh::lean_unsigned_to_nat(3);
                            v___x_5401_ =
                                l_Lean_Expr_isAppOfArity(v_e_5369_, v___x_5399_, v___x_5400_);
                            if v___x_5401_ == 0 {
                                v___x_5402_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_fn_5397_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                if leanh::lean_obj_tag(v___x_5402_) == 0 {
                                    v_a_5403_ = leanh::lean_ctor_get(v___x_5402_, 0);
                                    leanh::lean_inc(v_a_5403_);
                                    leanh::lean_dec_ref_known(v___x_5402_, 1);
                                    v___x_5404_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_arg_5398_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                    if leanh::lean_obj_tag(v___x_5404_) == 0 {
                                        v_a_5405_ = leanh::lean_ctor_get(v___x_5404_, 0);
                                        v_isSharedCheck_5413_ =
                                            (!leanh::lean_is_exclusive(v___x_5404_)) as u8;
                                        if v_isSharedCheck_5413_ == 0 {
                                            v___x_5407_ = v___x_5404_;
                                            v_isShared_5408_ = v_isSharedCheck_5413_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5405_);
                                            leanh::lean_dec(v___x_5404_);
                                            v___x_5407_ = leanh::lean_box(0);
                                            v_isShared_5408_ = v_isSharedCheck_5413_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_5403_);
                                        return v___x_5404_;
                                    }
                                } else {
                                    return v___x_5402_;
                                }
                            } else {
                                v___x_5414_ = l_Lean_Expr_appFn_x21(v_e_5369_);
                                v___x_5415_ = l_Lean_Expr_appArg_x21(v___x_5414_);
                                leanh::lean_dec_ref(v___x_5414_);
                                v___x_5416_ = l_Lean_Expr_appArg_x21(v_e_5369_);
                                v_l_5430_ = l_Lean_Expr_getAppFn_x27(v___x_5415_);
                                v_r_5431_ = l_Lean_Expr_getAppFn_x27(v___x_5416_);
                                v___x_5445_ = l_Lean_Expr_isMVar(v_l_5430_);
                                if v___x_5445_ == 0 {
                                    v___y_5441_ = v___x_5445_;
                                    state = 11;
                                    continue;
                                } else {
                                    v___x_5446_ = l_Lean_Expr_hasLooseBVars(v___x_5416_);
                                    v___y_5441_ = v___x_5446_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                        6 => {
                            v_binderType_5447_ = leanh::lean_ctor_get(v_e_5369_, 1);
                            v_body_5448_ = leanh::lean_ctor_get(v_e_5369_, 2);
                            v_ty_5376_ = v_binderType_5447_;
                            v_b_5377_ = v_body_5448_;
                            v___y_5378_ = v_a_5370_;
                            v___y_5379_ = v_a_5371_;
                            v___y_5380_ = v_a_5372_;
                            v___y_5381_ = v_a_5373_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderType_5449_ = leanh::lean_ctor_get(v_e_5369_, 1);
                            v_body_5450_ = leanh::lean_ctor_get(v_e_5369_, 2);
                            v_ty_5376_ = v_binderType_5449_;
                            v_b_5377_ = v_body_5450_;
                            v___y_5378_ = v_a_5370_;
                            v___y_5379_ = v_a_5371_;
                            v___y_5380_ = v_a_5372_;
                            v___y_5381_ = v_a_5373_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_type_5451_ = leanh::lean_ctor_get(v_e_5369_, 1);
                            v_value_5452_ = leanh::lean_ctor_get(v_e_5369_, 2);
                            v_body_5453_ = leanh::lean_ctor_get(v_e_5369_, 3);
                            v___x_5454_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_type_5451_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                            if leanh::lean_obj_tag(v___x_5454_) == 0 {
                                v_a_5455_ = leanh::lean_ctor_get(v___x_5454_, 0);
                                leanh::lean_inc(v_a_5455_);
                                leanh::lean_dec_ref_known(v___x_5454_, 1);
                                v___x_5456_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_value_5452_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                if leanh::lean_obj_tag(v___x_5456_) == 0 {
                                    v_a_5457_ = leanh::lean_ctor_get(v___x_5456_, 0);
                                    leanh::lean_inc(v_a_5457_);
                                    leanh::lean_dec_ref_known(v___x_5456_, 1);
                                    v___x_5458_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_body_5453_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                    if leanh::lean_obj_tag(v___x_5458_) == 0 {
                                        v_a_5459_ = leanh::lean_ctor_get(v___x_5458_, 0);
                                        v_isSharedCheck_5468_ =
                                            (!leanh::lean_is_exclusive(v___x_5458_)) as u8;
                                        if v_isSharedCheck_5468_ == 0 {
                                            v___x_5461_ = v___x_5458_;
                                            v_isShared_5462_ = v_isSharedCheck_5468_;
                                            state = 12;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5459_);
                                            leanh::lean_dec(v___x_5458_);
                                            v___x_5461_ = leanh::lean_box(0);
                                            v_isShared_5462_ = v_isSharedCheck_5468_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_5457_);
                                        leanh::lean_dec(v_a_5455_);
                                        return v___x_5458_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_5455_);
                                    return v___x_5456_;
                                }
                            } else {
                                return v___x_5454_;
                            }
                        }
                        10 => {
                            v_expr_5469_ = leanh::lean_ctor_get(v_e_5369_, 1);
                            v_e_5369_ = v_expr_5469_;
                            state = 0;
                            continue;
                        }
                        11 => {
                            v_struct_5471_ = leanh::lean_ctor_get(v_e_5369_, 2);
                            v_e_5369_ = v_struct_5471_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5473_ = leanh::lean_unsigned_to_nat(0);
                            v___x_5474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5474_, 0, v___x_5473_);
                            return v___x_5474_;
                        }
                    }
                }
            }
            1 => {
                v___x_5382_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_ty_5376_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
                if leanh::lean_obj_tag(v___x_5382_) == 0 {
                    v_a_5383_ = leanh::lean_ctor_get(v___x_5382_, 0);
                    leanh::lean_inc(v_a_5383_);
                    leanh::lean_dec_ref_known(v___x_5382_, 1);
                    v___x_5384_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_b_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
                    if leanh::lean_obj_tag(v___x_5384_) == 0 {
                        v_a_5385_ = leanh::lean_ctor_get(v___x_5384_, 0);
                        v_isSharedCheck_5393_ =
                            (!leanh::lean_is_exclusive(v___x_5384_)) as u8;
                        if v_isSharedCheck_5393_ == 0 {
                            v___x_5387_ = v___x_5384_;
                            v_isShared_5388_ = v_isSharedCheck_5393_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5385_);
                            leanh::lean_dec(v___x_5384_);
                            v___x_5387_ = leanh::lean_box(0);
                            v_isShared_5388_ = v_isSharedCheck_5393_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5383_);
                        return v___x_5384_;
                    }
                } else {
                    return v___x_5382_;
                }
            }
            2 => {
                v___x_5389_ = lean_nat_add(v_a_5383_, v_a_5385_);
                leanh::lean_dec(v_a_5385_);
                leanh::lean_dec(v_a_5383_);
                if v_isShared_5388_ == 0 {
                    leanh::lean_ctor_set(v___x_5387_, 0, v___x_5389_);
                    v___x_5391_ = v___x_5387_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
                    v___x_5391_ = v_reuseFailAlloc_5392_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5391_;
            }
            4 => {
                v___x_5409_ = lean_nat_add(v_a_5403_, v_a_5405_);
                leanh::lean_dec(v_a_5405_);
                leanh::lean_dec(v_a_5403_);
                if v_isShared_5408_ == 0 {
                    leanh::lean_ctor_set(v___x_5407_, 0, v___x_5409_);
                    v___x_5411_ = v___x_5407_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5409_);
                    v___x_5411_ = v_reuseFailAlloc_5412_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5411_;
            }
            6 => {
                v___x_5418_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v___x_5415_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                leanh::lean_dec_ref(v___x_5415_);
                if leanh::lean_obj_tag(v___x_5418_) == 0 {
                    v_a_5419_ = leanh::lean_ctor_get(v___x_5418_, 0);
                    leanh::lean_inc(v_a_5419_);
                    leanh::lean_dec_ref_known(v___x_5418_, 1);
                    v___x_5420_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v___x_5416_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                    leanh::lean_dec_ref(v___x_5416_);
                    if leanh::lean_obj_tag(v___x_5420_) == 0 {
                        v_a_5421_ = leanh::lean_ctor_get(v___x_5420_, 0);
                        v_isSharedCheck_5429_ =
                            (!leanh::lean_is_exclusive(v___x_5420_)) as u8;
                        if v_isSharedCheck_5429_ == 0 {
                            v___x_5423_ = v___x_5420_;
                            v_isShared_5424_ = v_isSharedCheck_5429_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5421_);
                            leanh::lean_dec(v___x_5420_);
                            v___x_5423_ = leanh::lean_box(0);
                            v_isShared_5424_ = v_isSharedCheck_5429_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_5419_);
                        return v___x_5420_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5416_);
                    return v___x_5418_;
                }
            }
            7 => {
                v___x_5425_ = lean_nat_add(v_a_5419_, v_a_5421_);
                leanh::lean_dec(v_a_5421_);
                leanh::lean_dec(v_a_5419_);
                if v_isShared_5424_ == 0 {
                    leanh::lean_ctor_set(v___x_5423_, 0, v___x_5425_);
                    v___x_5427_ = v___x_5423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5425_);
                    v___x_5427_ = v_reuseFailAlloc_5428_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5427_;
            }
            9 => {
                if v___y_5433_ == 0 {
                    leanh::lean_dec_ref(v_r_5431_);
                    state = 6;
                    continue;
                } else {
                    v___x_5434_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_5368_, v_r_5431_);
                    leanh::lean_dec_ref(v_r_5431_);
                    if v___x_5434_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_5416_);
                        leanh::lean_dec_ref(v___x_5415_);
                        v___x_5435_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5436_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5436_, 0, v___x_5435_);
                        return v___x_5436_;
                    }
                }
            }
            10 => {
                v___x_5438_ = l_Lean_Expr_isMVar(v_r_5431_);
                if v___x_5438_ == 0 {
                    v___y_5433_ = v___x_5438_;
                    state = 9;
                    continue;
                } else {
                    v___x_5439_ = l_Lean_Expr_hasLooseBVars(v___x_5415_);
                    v___y_5433_ = v___x_5439_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                if v___y_5441_ == 0 {
                    leanh::lean_dec_ref(v_l_5430_);
                    state = 10;
                    continue;
                } else {
                    v___x_5442_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_5368_, v_l_5430_);
                    leanh::lean_dec_ref(v_l_5430_);
                    if v___x_5442_ == 0 {
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_r_5431_);
                        leanh::lean_dec_ref(v___x_5416_);
                        leanh::lean_dec_ref(v___x_5415_);
                        v___x_5443_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5444_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5444_, 0, v___x_5443_);
                        return v___x_5444_;
                    }
                }
            }
            12 => {
                v___x_5463_ = lean_nat_add(v_a_5455_, v_a_5457_);
                leanh::lean_dec(v_a_5457_);
                leanh::lean_dec(v_a_5455_);
                v___x_5464_ = lean_nat_add(v___x_5463_, v_a_5459_);
                leanh::lean_dec(v_a_5459_);
                leanh::lean_dec(v___x_5463_);
                if v_isShared_5462_ == 0 {
                    leanh::lean_ctor_set(v___x_5461_, 0, v___x_5464_);
                    v___x_5466_ = v___x_5461_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
                    v___x_5466_ = v_reuseFailAlloc_5467_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___boxed(
    mut v_xs_5475_: *mut leanh::LeanObject,
    mut v_e_5476_: *mut leanh::LeanObject,
    mut v_a_5477_: *mut leanh::LeanObject,
    mut v_a_5478_: *mut leanh::LeanObject,
    mut v_a_5479_: *mut leanh::LeanObject,
    mut v_a_5480_: *mut leanh::LeanObject,
    mut v_a_5481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5475_, v_e_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_);
    leanh::lean_dec(v_a_5480_);
    leanh::lean_dec_ref(v_a_5479_);
    leanh::lean_dec(v_a_5478_);
    leanh::lean_dec_ref(v_a_5477_);
    leanh::lean_dec_ref(v_e_5476_);
    leanh::lean_dec_ref(v_xs_5475_);
    return v_res_5482_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(
    mut v_xs_5483_: *mut leanh::LeanObject,
    mut v_e_5484_: *mut leanh::LeanObject,
    mut v_a_5485_: *mut leanh::LeanObject,
    mut v_a_5486_: *mut leanh::LeanObject,
    mut v_a_5487_: *mut leanh::LeanObject,
    mut v_a_5488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5483_, v_e_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_);
    return v___x_5490_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars___boxed(
    mut v_xs_5491_: *mut leanh::LeanObject,
    mut v_e_5492_: *mut leanh::LeanObject,
    mut v_a_5493_: *mut leanh::LeanObject,
    mut v_a_5494_: *mut leanh::LeanObject,
    mut v_a_5495_: *mut leanh::LeanObject,
    mut v_a_5496_: *mut leanh::LeanObject,
    mut v_a_5497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5498_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(v_xs_5491_, v_e_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_);
    leanh::lean_dec(v_a_5496_);
    leanh::lean_dec_ref(v_a_5495_);
    leanh::lean_dec(v_a_5494_);
    leanh::lean_dec_ref(v_a_5493_);
    leanh::lean_dec_ref(v_e_5492_);
    leanh::lean_dec_ref(v_xs_5491_);
    return v_res_5498_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig() -> *mut leanh::LeanObject
{
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5501_: u8 = 0;
    let mut v_ctxApprox_5502_: u8 = 0;
    let mut v_quasiPatternApprox_5503_: u8 = 0;
    let mut v_constApprox_5504_: u8 = 0;
    let mut v_isDefEqStuckEx_5505_: u8 = 0;
    let mut v_unificationHints_5506_: u8 = 0;
    let mut v_proofIrrelevance_5507_: u8 = 0;
    let mut v_assignSyntheticOpaque_5508_: u8 = 0;
    let mut v_offsetCnstrs_5509_: u8 = 0;
    let mut v_transparency_5510_: u8 = 0;
    let mut v_etaStruct_5511_: u8 = 0;
    let mut v_univApprox_5512_: u8 = 0;
    let mut v_zetaUnused_5513_: u8 = 0;
    let mut v_zetaHave_5514_: u8 = 0;
    let mut v___x_5515_: u8 = 0;
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = l_Lean_Meta_simpGlobalConfig;
    v_config_5500_ = leanh::lean_ctor_get(v___x_5499_, 0);
    v_foApprox_5501_ = leanh::lean_ctor_get_uint8(v_config_5500_, 0 as u32);
    v_ctxApprox_5502_ = leanh::lean_ctor_get_uint8(v_config_5500_, 1 as u32);
    v_quasiPatternApprox_5503_ = leanh::lean_ctor_get_uint8(v_config_5500_, 2 as u32);
    v_constApprox_5504_ = leanh::lean_ctor_get_uint8(v_config_5500_, 3 as u32);
    v_isDefEqStuckEx_5505_ = leanh::lean_ctor_get_uint8(v_config_5500_, 4 as u32);
    v_unificationHints_5506_ = leanh::lean_ctor_get_uint8(v_config_5500_, 5 as u32);
    v_proofIrrelevance_5507_ = leanh::lean_ctor_get_uint8(v_config_5500_, 6 as u32);
    v_assignSyntheticOpaque_5508_ = leanh::lean_ctor_get_uint8(v_config_5500_, 7 as u32);
    v_offsetCnstrs_5509_ = leanh::lean_ctor_get_uint8(v_config_5500_, 8 as u32);
    v_transparency_5510_ = leanh::lean_ctor_get_uint8(v_config_5500_, 9 as u32);
    v_etaStruct_5511_ = leanh::lean_ctor_get_uint8(v_config_5500_, 10 as u32);
    v_univApprox_5512_ = leanh::lean_ctor_get_uint8(v_config_5500_, 11 as u32);
    v_zetaUnused_5513_ = leanh::lean_ctor_get_uint8(v_config_5500_, 17 as u32);
    v_zetaHave_5514_ = leanh::lean_ctor_get_uint8(v_config_5500_, 18 as u32);
    v___x_5515_ = 1;
    v___x_5516_ = 2;
    v___x_5517_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
    leanh::lean_ctor_set_uint8(v___x_5517_, 0 as u32, v_foApprox_5501_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 1 as u32, v_ctxApprox_5502_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 2 as u32, v_quasiPatternApprox_5503_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 3 as u32, v_constApprox_5504_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 4 as u32, v_isDefEqStuckEx_5505_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 5 as u32, v_unificationHints_5506_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 6 as u32, v_proofIrrelevance_5507_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 7 as u32, v_assignSyntheticOpaque_5508_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 8 as u32, v_offsetCnstrs_5509_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 9 as u32, v_transparency_5510_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 10 as u32, v_etaStruct_5511_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 11 as u32, v_univApprox_5512_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 12 as u32, v___x_5515_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 13 as u32, v___x_5515_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 14 as u32, v___x_5516_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 15 as u32, v___x_5515_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 16 as u32, v___x_5515_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 17 as u32, v_zetaUnused_5513_);
    leanh::lean_ctor_set_uint8(v___x_5517_, 18 as u32, v_zetaHave_5514_);
    v___x_5518_ = l_Lean_Meta_Config_toConfigWithKey(v___x_5517_);
    return v___x_5518_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(
    mut v_k_5519_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_5520_: u8,
    mut v___y_5521_: *mut leanh::LeanObject,
    mut v___y_5522_: *mut leanh::LeanObject,
    mut v___y_5523_: *mut leanh::LeanObject,
    mut v___y_5524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5530_: u8 = 0;
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5534_: u8 = 0;
    let mut v_a_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_5520_,
                    v_k_5519_,
                    v___y_5521_,
                    v___y_5522_,
                    v___y_5523_,
                    v___y_5524_,
                );
                if leanh::lean_obj_tag(v___x_5526_) == 0 {
                    v_a_5527_ = leanh::lean_ctor_get(v___x_5526_, 0);
                    v_isSharedCheck_5534_ = (!leanh::lean_is_exclusive(v___x_5526_)) as u8;
                    if v_isSharedCheck_5534_ == 0 {
                        v___x_5529_ = v___x_5526_;
                        v_isShared_5530_ = v_isSharedCheck_5534_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5527_);
                        leanh::lean_dec(v___x_5526_);
                        v___x_5529_ = leanh::lean_box(0);
                        v_isShared_5530_ = v_isSharedCheck_5534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5535_ = leanh::lean_ctor_get(v___x_5526_, 0);
                    v_isSharedCheck_5542_ = (!leanh::lean_is_exclusive(v___x_5526_)) as u8;
                    if v_isSharedCheck_5542_ == 0 {
                        v___x_5537_ = v___x_5526_;
                        v_isShared_5538_ = v_isSharedCheck_5542_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5535_);
                        leanh::lean_dec(v___x_5526_);
                        v___x_5537_ = leanh::lean_box(0);
                        v_isShared_5538_ = v_isSharedCheck_5542_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5530_ == 0 {
                    v___x_5532_ = v___x_5529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
                    v___x_5532_ = v_reuseFailAlloc_5533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5532_;
            }
            3 => {
                if v_isShared_5538_ == 0 {
                    v___x_5540_ = v___x_5537_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
                    v___x_5540_ = v_reuseFailAlloc_5541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg___boxed(
    mut v_k_5543_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_5544_: *mut leanh::LeanObject,
    mut v___y_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
    mut v___y_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_5550_: u8 = 0;
    let mut v_res_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_5550_ =
        (leanh::lean_unbox(v_allowLevelAssignments_5544_) as u8);
    v_res_5551_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_5543_, v_allowLevelAssignments_boxed_5550_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_);
    leanh::lean_dec(v___y_5548_);
    leanh::lean_dec_ref(v___y_5547_);
    leanh::lean_dec(v___y_5546_);
    leanh::lean_dec_ref(v___y_5545_);
    return v_res_5551_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(
    mut v_00_u03b1_5552_: *mut leanh::LeanObject,
    mut v_k_5553_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_5554_: u8,
    mut v___y_5555_: *mut leanh::LeanObject,
    mut v___y_5556_: *mut leanh::LeanObject,
    mut v___y_5557_: *mut leanh::LeanObject,
    mut v___y_5558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5560_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_5553_, v_allowLevelAssignments_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
    return v___x_5560_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(
    mut v_00_u03b1_5561_: *mut leanh::LeanObject,
    mut v_k_5562_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
    mut v___y_5566_: *mut leanh::LeanObject,
    mut v___y_5567_: *mut leanh::LeanObject,
    mut v___y_5568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_5569_: u8 = 0;
    let mut v_res_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_5569_ =
        (leanh::lean_unbox(v_allowLevelAssignments_5563_) as u8);
    v_res_5570_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(v_00_u03b1_5561_, v_k_5562_, v_allowLevelAssignments_boxed_5569_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_);
    leanh::lean_dec(v___y_5567_);
    leanh::lean_dec_ref(v___y_5566_);
    leanh::lean_dec(v___y_5565_);
    leanh::lean_dec_ref(v___y_5564_);
    return v_res_5570_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(
    mut v___x_5571_: *mut leanh::LeanObject,
    mut v___x_5572_: *mut leanh::LeanObject,
    mut v_fst_5573_: *mut leanh::LeanObject,
    mut v___x_5574_: *mut leanh::LeanObject,
    mut v_expr_5575_: *mut leanh::LeanObject,
    mut v_____r_5576_: *mut leanh::LeanObject,
    mut v_lastSuccess_5577_: *mut leanh::LeanObject,
    mut v_boundAssignments_5578_: *mut leanh::LeanObject,
    mut v___y_5579_: *mut leanh::LeanObject,
    mut v___y_5580_: *mut leanh::LeanObject,
    mut v___y_5581_: *mut leanh::LeanObject,
    mut v___y_5582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5592_: u8 = 0;
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut v_a_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5584_ = leanh::lean_unsigned_to_nat(2);
                v___x_5585_ = lean_nat_sub(v___x_5571_, v___x_5584_);
                v___x_5586_ = lean_nat_sub(v___x_5585_, v___x_5572_);
                leanh::lean_dec(v___x_5585_);
                v___x_5587_ = l_Lean_Expr_getRevArg_x21(v_fst_5573_, v___x_5586_);
                v___x_5588_ = l_Lean_Meta_whnfR(
                    v___x_5587_,
                    v___y_5579_,
                    v___y_5580_,
                    v___y_5581_,
                    v___y_5582_,
                );
                if leanh::lean_obj_tag(v___x_5588_) == 0 {
                    v_a_5589_ = leanh::lean_ctor_get(v___x_5588_, 0);
                    v_isSharedCheck_5601_ = (!leanh::lean_is_exclusive(v___x_5588_)) as u8;
                    if v_isSharedCheck_5601_ == 0 {
                        v___x_5591_ = v___x_5588_;
                        v_isShared_5592_ = v_isSharedCheck_5601_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5589_);
                        leanh::lean_dec(v___x_5588_);
                        v___x_5591_ = leanh::lean_box(0);
                        v_isShared_5592_ = v_isSharedCheck_5601_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_boundAssignments_5578_);
                    leanh::lean_dec(v_lastSuccess_5577_);
                    leanh::lean_dec_ref(v_expr_5575_);
                    leanh::lean_dec(v___x_5574_);
                    v_a_5602_ = leanh::lean_ctor_get(v___x_5588_, 0);
                    v_isSharedCheck_5609_ = (!leanh::lean_is_exclusive(v___x_5588_)) as u8;
                    if v_isSharedCheck_5609_ == 0 {
                        v___x_5604_ = v___x_5588_;
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5602_);
                        leanh::lean_dec(v___x_5588_);
                        v___x_5604_ = leanh::lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5593_, 0, v_lastSuccess_5577_);
                leanh::lean_ctor_set(v___x_5593_, 1, v_boundAssignments_5578_);
                v___x_5594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5594_, 0, v___x_5574_);
                leanh::lean_ctor_set(v___x_5594_, 1, v___x_5593_);
                v___x_5595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5595_, 0, v_expr_5575_);
                leanh::lean_ctor_set(v___x_5595_, 1, v___x_5594_);
                v___x_5596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5596_, 0, v_a_5589_);
                leanh::lean_ctor_set(v___x_5596_, 1, v___x_5595_);
                v___x_5597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5597_, 0, v___x_5596_);
                if v_isShared_5592_ == 0 {
                    leanh::lean_ctor_set(v___x_5591_, 0, v___x_5597_);
                    v___x_5599_ = v___x_5591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5600_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5597_);
                    v___x_5599_ = v_reuseFailAlloc_5600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5599_;
            }
            3 => {
                if v_isShared_5605_ == 0 {
                    v___x_5607_ = v___x_5604_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
                    v___x_5607_ = v_reuseFailAlloc_5608_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0___boxed(
    mut v___x_5610_: *mut leanh::LeanObject,
    mut v___x_5611_: *mut leanh::LeanObject,
    mut v_fst_5612_: *mut leanh::LeanObject,
    mut v___x_5613_: *mut leanh::LeanObject,
    mut v_expr_5614_: *mut leanh::LeanObject,
    mut v_____r_5615_: *mut leanh::LeanObject,
    mut v_lastSuccess_5616_: *mut leanh::LeanObject,
    mut v_boundAssignments_5617_: *mut leanh::LeanObject,
    mut v___y_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
    mut v___y_5620_: *mut leanh::LeanObject,
    mut v___y_5621_: *mut leanh::LeanObject,
    mut v___y_5622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5623_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_5610_, v___x_5611_, v_fst_5612_, v___x_5613_, v_expr_5614_, v_____r_5615_, v_lastSuccess_5616_, v_boundAssignments_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    leanh::lean_dec(v___y_5621_);
    leanh::lean_dec_ref(v___y_5620_);
    leanh::lean_dec(v___y_5619_);
    leanh::lean_dec_ref(v___y_5618_);
    leanh::lean_dec(v_fst_5612_);
    leanh::lean_dec(v___x_5611_);
    leanh::lean_dec(v___x_5610_);
    return v_res_5623_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5631_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5631_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4);
    v___x_5633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5633_, 0, v___x_5632_);
    return v___x_5633_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5634_ = leanh::lean_unsigned_to_nat(0);
    v___x_5635_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
    v___x_5636_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5636_, 0, v___x_5635_);
    leanh::lean_ctor_set(v___x_5636_, 1, v___x_5634_);
    return v___x_5636_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5637_ = leanh::lean_unsigned_to_nat(32);
    v___x_5638_ = lean_mk_empty_array_with_capacity(v___x_5637_);
    v___x_5639_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5639_, 0, v___x_5638_);
    return v___x_5639_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_5640_: usize = 0;
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5640_ = 5usize;
    v___x_5641_ = leanh::lean_unsigned_to_nat(0);
    v___x_5642_ = leanh::lean_unsigned_to_nat(32);
    v___x_5643_ = lean_mk_empty_array_with_capacity(v___x_5642_);
    v___x_5644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7);
    v___x_5645_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5645_, 0, v___x_5644_);
    leanh::lean_ctor_set(v___x_5645_, 1, v___x_5643_);
    leanh::lean_ctor_set(v___x_5645_, 2, v___x_5641_);
    leanh::lean_ctor_set(v___x_5645_, 3, v___x_5641_);
    leanh::lean_ctor_set_usize(v___x_5645_, 4, v___x_5640_);
    return v___x_5645_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5646_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8);
    v___x_5647_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
    v___x_5648_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5648_, 0, v___x_5647_);
    leanh::lean_ctor_set(v___x_5648_, 1, v___x_5647_);
    leanh::lean_ctor_set(v___x_5648_, 2, v___x_5647_);
    leanh::lean_ctor_set(v___x_5648_, 3, v___x_5646_);
    return v___x_5648_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5649_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9);
    v___x_5650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6);
    v___x_5651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5651_, 0, v___x_5650_);
    leanh::lean_ctor_set(v___x_5651_, 1, v___x_5649_);
    return v___x_5651_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(
    mut v_a_5652_: *mut leanh::LeanObject,
    mut v_xs_5653_: *mut leanh::LeanObject,
    mut v_a_5654_: *mut leanh::LeanObject,
    mut v___y_5655_: *mut leanh::LeanObject,
    mut v___y_5656_: *mut leanh::LeanObject,
    mut v___y_5657_: *mut leanh::LeanObject,
    mut v___y_5658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v_a_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v_a_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5676_: u8 = 0;
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut v_snd_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v_fst_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5691_: u8 = 0;
    let mut v_fst_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5695_: u8 = 0;
    let mut v_fst_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: u8 = 0;
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: u8 = 0;
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: u8 = 0;
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5751_: u8 = 0;
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5755_: u8 = 0;
    let mut v_a_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5763_: u8 = 0;
    let mut v_a_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5767_: u8 = 0;
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5771_: u8 = 0;
    let mut v_isSharedCheck_5772_: u8 = 0;
    let mut v_isSharedCheck_5773_: u8 = 0;
    let mut v_unused_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v_unused_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5777_: u8 = 0;
    let mut v_unused_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_5681_ = leanh::lean_ctor_get(v_a_5654_, 1);
                leanh::lean_inc(v_snd_5681_);
                v_snd_5682_ = leanh::lean_ctor_get(v_snd_5681_, 1);
                leanh::lean_inc(v_snd_5682_);
                v_snd_5683_ = leanh::lean_ctor_get(v_snd_5682_, 1);
                leanh::lean_inc(v_snd_5683_);
                v_fst_5684_ = leanh::lean_ctor_get(v_a_5654_, 0);
                v_isSharedCheck_5777_ = (!leanh::lean_is_exclusive(v_a_5654_)) as u8;
                if v_isSharedCheck_5777_ == 0 {
                    v_unused_5778_ = leanh::lean_ctor_get(v_a_5654_, 1);
                    leanh::lean_dec(v_unused_5778_);
                    v___x_5686_ = v_a_5654_;
                    v_isShared_5687_ = v_isSharedCheck_5777_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5684_);
                    leanh::lean_dec(v_a_5654_);
                    v___x_5686_ = leanh::lean_box(0);
                    v_isShared_5687_ = v_isSharedCheck_5777_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_5661_) == 0 {
                    v_a_5662_ = leanh::lean_ctor_get(v___y_5661_, 0);
                    v_isSharedCheck_5672_ = (!leanh::lean_is_exclusive(v___y_5661_)) as u8;
                    if v_isSharedCheck_5672_ == 0 {
                        v___x_5664_ = v___y_5661_;
                        v_isShared_5665_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5662_);
                        leanh::lean_dec(v___y_5661_);
                        v___x_5664_ = leanh::lean_box(0);
                        v_isShared_5665_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_5652_);
                    v_a_5673_ = leanh::lean_ctor_get(v___y_5661_, 0);
                    v_isSharedCheck_5680_ = (!leanh::lean_is_exclusive(v___y_5661_)) as u8;
                    if v_isSharedCheck_5680_ == 0 {
                        v___x_5675_ = v___y_5661_;
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5673_);
                        leanh::lean_dec(v___y_5661_);
                        v___x_5675_ = leanh::lean_box(0);
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5662_) == 0 {
                    leanh::lean_dec_ref(v_a_5652_);
                    v_a_5666_ = leanh::lean_ctor_get(v_a_5662_, 0);
                    leanh::lean_inc(v_a_5666_);
                    leanh::lean_dec_ref_known(v_a_5662_, 1);
                    if v_isShared_5665_ == 0 {
                        leanh::lean_ctor_set(v___x_5664_, 0, v_a_5666_);
                        v___x_5668_ = v___x_5664_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5666_);
                        v___x_5668_ = v_reuseFailAlloc_5669_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5664_);
                    v_a_5670_ = leanh::lean_ctor_get(v_a_5662_, 0);
                    leanh::lean_inc(v_a_5670_);
                    leanh::lean_dec_ref_known(v_a_5662_, 1);
                    v_a_5654_ = v_a_5670_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_5668_;
            }
            4 => {
                if v_isShared_5676_ == 0 {
                    v___x_5678_ = v___x_5675_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5673_);
                    v___x_5678_ = v_reuseFailAlloc_5679_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5678_;
            }
            6 => {
                v_fst_5688_ = leanh::lean_ctor_get(v_snd_5681_, 0);
                v_isSharedCheck_5775_ = (!leanh::lean_is_exclusive(v_snd_5681_)) as u8;
                if v_isSharedCheck_5775_ == 0 {
                    v_unused_5776_ = leanh::lean_ctor_get(v_snd_5681_, 1);
                    leanh::lean_dec(v_unused_5776_);
                    v___x_5690_ = v_snd_5681_;
                    v_isShared_5691_ = v_isSharedCheck_5775_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5688_);
                    leanh::lean_dec(v_snd_5681_);
                    v___x_5690_ = leanh::lean_box(0);
                    v_isShared_5691_ = v_isSharedCheck_5775_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_5692_ = leanh::lean_ctor_get(v_snd_5682_, 0);
                v_isSharedCheck_5773_ = (!leanh::lean_is_exclusive(v_snd_5682_)) as u8;
                if v_isSharedCheck_5773_ == 0 {
                    v_unused_5774_ = leanh::lean_ctor_get(v_snd_5682_, 1);
                    leanh::lean_dec(v_unused_5774_);
                    v___x_5694_ = v_snd_5682_;
                    v_isShared_5695_ = v_isSharedCheck_5773_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5692_);
                    leanh::lean_dec(v_snd_5682_);
                    v___x_5694_ = leanh::lean_box(0);
                    v_isShared_5695_ = v_isSharedCheck_5773_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_5696_ = leanh::lean_ctor_get(v_snd_5683_, 0);
                v_snd_5697_ = leanh::lean_ctor_get(v_snd_5683_, 1);
                v_isSharedCheck_5772_ = (!leanh::lean_is_exclusive(v_snd_5683_)) as u8;
                if v_isSharedCheck_5772_ == 0 {
                    v___x_5699_ = v_snd_5683_;
                    v_isShared_5700_ = v_isSharedCheck_5772_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5697_);
                    leanh::lean_inc(v_fst_5696_);
                    leanh::lean_dec(v_snd_5683_);
                    v___x_5699_ = leanh::lean_box(0);
                    v_isShared_5700_ = v_isSharedCheck_5772_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5701_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2;
                v___x_5702_ = leanh::lean_unsigned_to_nat(3);
                v___x_5703_ = l_Lean_Expr_isAppOfArity(v_fst_5684_, v___x_5701_, v___x_5702_);
                if v___x_5703_ == 0 {
                    leanh::lean_dec_ref(v_a_5652_);
                    if v_isShared_5700_ == 0 {
                        v___x_5705_ = v___x_5699_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_fst_5696_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_snd_5697_);
                        v___x_5705_ = v_reuseFailAlloc_5716_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5699_);
                    leanh::lean_del_object(v___x_5694_);
                    leanh::lean_del_object(v___x_5690_);
                    leanh::lean_del_object(v___x_5686_);
                    v___x_5717_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5718_ = l_Lean_Expr_getAppNumArgs(v_fst_5684_);
                    v___x_5719_ = lean_nat_sub(v___x_5718_, v___x_5717_);
                    v___x_5720_ = lean_nat_sub(v___x_5719_, v___x_5717_);
                    leanh::lean_dec(v___x_5719_);
                    v___x_5721_ = l_Lean_Expr_getRevArg_x21(v_fst_5684_, v___x_5720_);
                    v___x_5722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5722_, 0, v___x_5721_);
                    v___x_5723_ = 0;
                    v___x_5724_ = leanh::lean_box(0);
                    v___x_5725_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_5722_,
                        v___x_5723_,
                        v___x_5724_,
                        v___y_5655_,
                        v___y_5656_,
                        v___y_5657_,
                        v___y_5658_,
                    );
                    if leanh::lean_obj_tag(v___x_5725_) == 0 {
                        v_a_5726_ = leanh::lean_ctor_get(v___x_5725_, 0);
                        leanh::lean_inc(v_a_5726_);
                        leanh::lean_dec_ref_known(v___x_5725_, 1);
                        v___x_5727_ = lean_mk_empty_array_with_capacity(v___x_5717_);
                        v___x_5728_ = lean_array_push(v___x_5727_, v_a_5726_);
                        v___x_5729_ = l_Lean_Expr_beta(v_fst_5688_, v___x_5728_);
                        v___x_5730_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3;
                        v___x_5731_ = leanh::lean_box(0);
                        v___x_5732_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10);
                        leanh::lean_inc_ref(v_a_5652_);
                        v___x_5733_ = l_Lean_Meta_simp(
                            v___x_5729_,
                            v_a_5652_,
                            v___x_5730_,
                            v___x_5731_,
                            v___x_5732_,
                            v___y_5655_,
                            v___y_5656_,
                            v___y_5657_,
                            v___y_5658_,
                        );
                        if leanh::lean_obj_tag(v___x_5733_) == 0 {
                            v_a_5734_ = leanh::lean_ctor_get(v___x_5733_, 0);
                            leanh::lean_inc(v_a_5734_);
                            leanh::lean_dec_ref_known(v___x_5733_, 1);
                            v_fst_5735_ = leanh::lean_ctor_get(v_a_5734_, 0);
                            leanh::lean_inc(v_fst_5735_);
                            leanh::lean_dec(v_a_5734_);
                            v_expr_5736_ = leanh::lean_ctor_get(v_fst_5735_, 0);
                            leanh::lean_inc_ref(v_expr_5736_);
                            leanh::lean_dec(v_fst_5735_);
                            v___x_5737_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5653_, v_expr_5736_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
                            if leanh::lean_obj_tag(v___x_5737_) == 0 {
                                v_a_5738_ = leanh::lean_ctor_get(v___x_5737_, 0);
                                leanh::lean_inc(v_a_5738_);
                                leanh::lean_dec_ref_known(v___x_5737_, 1);
                                v___x_5739_ = lean_nat_add(v_fst_5692_, v___x_5717_);
                                leanh::lean_dec(v_fst_5692_);
                                v___x_5743_ = lean_nat_dec_lt(v_a_5738_, v_snd_5697_);
                                if v___x_5743_ == 0 {
                                    v___x_5744_ = l_Lean_Expr_getAppFn_x27(v_expr_5736_);
                                    v___x_5745_ = l_Lean_Expr_isMVar(v___x_5744_);
                                    leanh::lean_dec_ref(v___x_5744_);
                                    if v___x_5745_ == 0 {
                                        leanh::lean_dec(v_a_5738_);
                                        v___x_5746_ = leanh::lean_box(0);
                                        v___x_5747_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_5718_, v___x_5717_, v_fst_5684_, v___x_5739_, v_expr_5736_, v___x_5746_, v_fst_5696_, v_snd_5697_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
                                        leanh::lean_dec(v_fst_5684_);
                                        leanh::lean_dec(v___x_5718_);
                                        v___y_5661_ = v___x_5747_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_snd_5697_);
                                        leanh::lean_dec(v_fst_5696_);
                                        state = 14;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_snd_5697_);
                                    leanh::lean_dec(v_fst_5696_);
                                    state = 14;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_expr_5736_);
                                leanh::lean_dec(v___x_5718_);
                                leanh::lean_dec(v_snd_5697_);
                                leanh::lean_dec(v_fst_5696_);
                                leanh::lean_dec(v_fst_5692_);
                                leanh::lean_dec(v_fst_5684_);
                                leanh::lean_dec_ref(v_a_5652_);
                                v_a_5748_ = leanh::lean_ctor_get(v___x_5737_, 0);
                                v_isSharedCheck_5755_ =
                                    (!leanh::lean_is_exclusive(v___x_5737_)) as u8;
                                if v_isSharedCheck_5755_ == 0 {
                                    v___x_5750_ = v___x_5737_;
                                    v_isShared_5751_ = v_isSharedCheck_5755_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5748_);
                                    leanh::lean_dec(v___x_5737_);
                                    v___x_5750_ = leanh::lean_box(0);
                                    v_isShared_5751_ = v_isSharedCheck_5755_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_5718_);
                            leanh::lean_dec(v_snd_5697_);
                            leanh::lean_dec(v_fst_5696_);
                            leanh::lean_dec(v_fst_5692_);
                            leanh::lean_dec(v_fst_5684_);
                            leanh::lean_dec_ref(v_a_5652_);
                            v_a_5756_ = leanh::lean_ctor_get(v___x_5733_, 0);
                            v_isSharedCheck_5763_ =
                                (!leanh::lean_is_exclusive(v___x_5733_)) as u8;
                            if v_isSharedCheck_5763_ == 0 {
                                v___x_5758_ = v___x_5733_;
                                v_isShared_5759_ = v_isSharedCheck_5763_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5756_);
                                leanh::lean_dec(v___x_5733_);
                                v___x_5758_ = leanh::lean_box(0);
                                v_isShared_5759_ = v_isSharedCheck_5763_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_5718_);
                        leanh::lean_dec(v_snd_5697_);
                        leanh::lean_dec(v_fst_5696_);
                        leanh::lean_dec(v_fst_5692_);
                        leanh::lean_dec(v_fst_5688_);
                        leanh::lean_dec(v_fst_5684_);
                        leanh::lean_dec_ref(v_a_5652_);
                        v_a_5764_ = leanh::lean_ctor_get(v___x_5725_, 0);
                        v_isSharedCheck_5771_ =
                            (!leanh::lean_is_exclusive(v___x_5725_)) as u8;
                        if v_isSharedCheck_5771_ == 0 {
                            v___x_5766_ = v___x_5725_;
                            v_isShared_5767_ = v_isSharedCheck_5771_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5764_);
                            leanh::lean_dec(v___x_5725_);
                            v___x_5766_ = leanh::lean_box(0);
                            v_isShared_5767_ = v_isSharedCheck_5771_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_5695_ == 0 {
                    leanh::lean_ctor_set(v___x_5694_, 1, v___x_5705_);
                    v___x_5707_ = v___x_5694_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_fst_5692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 1, v___x_5705_);
                    v___x_5707_ = v_reuseFailAlloc_5715_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5691_ == 0 {
                    leanh::lean_ctor_set(v___x_5690_, 1, v___x_5707_);
                    v___x_5709_ = v___x_5690_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5714_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_fst_5688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 1, v___x_5707_);
                    v___x_5709_ = v_reuseFailAlloc_5714_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_5687_ == 0 {
                    leanh::lean_ctor_set(v___x_5686_, 1, v___x_5709_);
                    v___x_5711_ = v___x_5686_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5713_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_fst_5684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5709_);
                    v___x_5711_ = v_reuseFailAlloc_5713_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5712_, 0, v___x_5711_);
                return v___x_5712_;
            }
            14 => {
                v___x_5741_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_5739_);
                v___x_5742_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_5718_, v___x_5717_, v_fst_5684_, v___x_5739_, v_expr_5736_, v___x_5741_, v___x_5739_, v_a_5738_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
                leanh::lean_dec(v_fst_5684_);
                leanh::lean_dec(v___x_5718_);
                v___y_5661_ = v___x_5742_;
                state = 1;
                continue;
            }
            15 => {
                if v_isShared_5751_ == 0 {
                    v___x_5753_ = v___x_5750_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
                    v___x_5753_ = v_reuseFailAlloc_5754_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5753_;
            }
            17 => {
                if v_isShared_5759_ == 0 {
                    v___x_5761_ = v___x_5758_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5762_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_a_5756_);
                    v___x_5761_ = v_reuseFailAlloc_5762_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5761_;
            }
            19 => {
                if v_isShared_5767_ == 0 {
                    v___x_5769_ = v___x_5766_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_a_5764_);
                    v___x_5769_ = v_reuseFailAlloc_5770_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___boxed(
    mut v_a_5779_: *mut leanh::LeanObject,
    mut v_xs_5780_: *mut leanh::LeanObject,
    mut v_a_5781_: *mut leanh::LeanObject,
    mut v___y_5782_: *mut leanh::LeanObject,
    mut v___y_5783_: *mut leanh::LeanObject,
    mut v___y_5784_: *mut leanh::LeanObject,
    mut v___y_5785_: *mut leanh::LeanObject,
    mut v___y_5786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5787_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_5779_, v_xs_5780_, v_a_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
    leanh::lean_dec(v___y_5785_);
    leanh::lean_dec_ref(v___y_5784_);
    leanh::lean_dec(v___y_5783_);
    leanh::lean_dec_ref(v___y_5782_);
    leanh::lean_dec_ref(v_xs_5780_);
    return v_res_5787_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(
    mut v___x_5788_: *mut leanh::LeanObject,
    mut v___x_5789_: u8,
    mut v_00_u03c3s_5790_: *mut leanh::LeanObject,
    mut v_xs_5791_: *mut leanh::LeanObject,
    mut v_e_5792_: *mut leanh::LeanObject,
    mut v___y_5793_: *mut leanh::LeanObject,
    mut v___y_5794_: *mut leanh::LeanObject,
    mut v___y_5795_: *mut leanh::LeanObject,
    mut v___y_5796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5801_: u8 = 0;
    let mut v_trackZetaDelta_5802_: u8 = 0;
    let mut v_zetaDeltaSet_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5809_: u8 = 0;
    let mut v_inTypeClassResolution_5810_: u8 = 0;
    let mut v_cacheInferType_5811_: u8 = 0;
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5814_: u8 = 0;
    let mut v___x_5815_: u64 = 0;
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v_snd_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_a_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5847_: u8 = 0;
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5851_: u8 = 0;
    let mut v_a_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5855_: u8 = 0;
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5859_: u8 = 0;
    let mut v_a_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5867_: u8 = 0;
    let mut v_reuseFailAlloc_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_unused_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5872_: u8 = 0;
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_5789_ == 0 {
                    v_config_5798_ = leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5872_ = (!leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5872_ == 0 {
                        v___x_5800_ = v___x_5788_;
                        v_isShared_5801_ = v_isSharedCheck_5872_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_config_5798_);
                        leanh::lean_dec(v___x_5788_);
                        v___x_5800_ = leanh::lean_box(0);
                        v_isShared_5801_ = v_isSharedCheck_5872_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5793_);
                    leanh::lean_dec_ref(v_e_5792_);
                    leanh::lean_dec_ref(v_00_u03c3s_5790_);
                    leanh::lean_dec_ref(v___x_5788_);
                    v___x_5873_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5874_, 0, v___x_5873_);
                    return v___x_5874_;
                }
            }
            1 => {
                v_trackZetaDelta_5802_ = leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5803_ = leanh::lean_ctor_get(v___y_5793_, 1);
                v_lctx_5804_ = leanh::lean_ctor_get(v___y_5793_, 2);
                v_localInstances_5805_ = leanh::lean_ctor_get(v___y_5793_, 3);
                v_defEqCtx_x3f_5806_ = leanh::lean_ctor_get(v___y_5793_, 4);
                v_synthPendingDepth_5807_ = leanh::lean_ctor_get(v___y_5793_, 5);
                v_canUnfold_x3f_5808_ = leanh::lean_ctor_get(v___y_5793_, 6);
                v_univApprox_5809_ = leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5810_ = leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5811_ = leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v_isSharedCheck_5870_ = (!leanh::lean_is_exclusive(v___y_5793_)) as u8;
                if v_isSharedCheck_5870_ == 0 {
                    v_unused_5871_ = leanh::lean_ctor_get(v___y_5793_, 0);
                    leanh::lean_dec(v_unused_5871_);
                    v___x_5813_ = v___y_5793_;
                    v_isShared_5814_ = v_isSharedCheck_5870_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_canUnfold_x3f_5808_);
                    leanh::lean_inc(v_synthPendingDepth_5807_);
                    leanh::lean_inc(v_defEqCtx_x3f_5806_);
                    leanh::lean_inc(v_localInstances_5805_);
                    leanh::lean_inc(v_lctx_5804_);
                    leanh::lean_inc(v_zetaDeltaSet_5803_);
                    leanh::lean_dec(v___y_5793_);
                    v___x_5813_ = leanh::lean_box(0);
                    v_isShared_5814_ = v_isSharedCheck_5870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5815_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_5798_);
                if v_isShared_5801_ == 0 {
                    v___x_5817_ = v___x_5800_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5869_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_config_5798_);
                    v___x_5817_ = v_reuseFailAlloc_5869_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint64(
                    v___x_5817_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5815_,
                );
                if v_isShared_5814_ == 0 {
                    leanh::lean_ctor_set(v___x_5813_, 0, v___x_5817_);
                    v___x_5819_ = v___x_5813_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5868_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_zetaDeltaSet_5803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_lctx_5804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 3, v_localInstances_5805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_defEqCtx_x3f_5806_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5868_,
                        5,
                        v_synthPendingDepth_5807_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 6, v_canUnfold_x3f_5808_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_5802_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_5809_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_5810_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_5811_,
                    );
                    v___x_5819_ = v_reuseFailAlloc_5868_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5820_ = l_Lean_Meta_Simp_Context_mkDefault___redArg(
                    v___x_5819_,
                    v___y_5795_,
                    v___y_5796_,
                );
                if leanh::lean_obj_tag(v___x_5820_) == 0 {
                    v_a_5821_ = leanh::lean_ctor_get(v___x_5820_, 0);
                    leanh::lean_inc(v_a_5821_);
                    leanh::lean_dec_ref_known(v___x_5820_, 1);
                    v___x_5822_ = l_Lean_Meta_whnfR(
                        v_00_u03c3s_5790_,
                        v___x_5819_,
                        v___y_5794_,
                        v___y_5795_,
                        v___y_5796_,
                    );
                    if leanh::lean_obj_tag(v___x_5822_) == 0 {
                        v_a_5823_ = leanh::lean_ctor_get(v___x_5822_, 0);
                        leanh::lean_inc(v_a_5823_);
                        leanh::lean_dec_ref_known(v___x_5822_, 1);
                        v___x_5824_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5791_, v_e_5792_, v___x_5819_, v___y_5794_, v___y_5795_, v___y_5796_);
                        if leanh::lean_obj_tag(v___x_5824_) == 0 {
                            v_a_5825_ = leanh::lean_ctor_get(v___x_5824_, 0);
                            leanh::lean_inc(v_a_5825_);
                            leanh::lean_dec_ref_known(v___x_5824_, 1);
                            v___x_5826_ = leanh::lean_unsigned_to_nat(0);
                            v___x_5827_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5827_, 0, v___x_5826_);
                            leanh::lean_ctor_set(v___x_5827_, 1, v_a_5825_);
                            v___x_5828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5828_, 0, v___x_5826_);
                            leanh::lean_ctor_set(v___x_5828_, 1, v___x_5827_);
                            v___x_5829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5829_, 0, v_e_5792_);
                            leanh::lean_ctor_set(v___x_5829_, 1, v___x_5828_);
                            v___x_5830_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5830_, 0, v_a_5823_);
                            leanh::lean_ctor_set(v___x_5830_, 1, v___x_5829_);
                            v___x_5831_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_5821_, v_xs_5791_, v___x_5830_, v___x_5819_, v___y_5794_, v___y_5795_, v___y_5796_);
                            leanh::lean_dec_ref(v___x_5819_);
                            if leanh::lean_obj_tag(v___x_5831_) == 0 {
                                v_a_5832_ = leanh::lean_ctor_get(v___x_5831_, 0);
                                v_isSharedCheck_5843_ =
                                    (!leanh::lean_is_exclusive(v___x_5831_)) as u8;
                                if v_isSharedCheck_5843_ == 0 {
                                    v___x_5834_ = v___x_5831_;
                                    v_isShared_5835_ = v_isSharedCheck_5843_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5832_);
                                    leanh::lean_dec(v___x_5831_);
                                    v___x_5834_ = leanh::lean_box(0);
                                    v_isShared_5835_ = v_isSharedCheck_5843_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_5844_ = leanh::lean_ctor_get(v___x_5831_, 0);
                                v_isSharedCheck_5851_ =
                                    (!leanh::lean_is_exclusive(v___x_5831_)) as u8;
                                if v_isSharedCheck_5851_ == 0 {
                                    v___x_5846_ = v___x_5831_;
                                    v_isShared_5847_ = v_isSharedCheck_5851_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5844_);
                                    leanh::lean_dec(v___x_5831_);
                                    v___x_5846_ = leanh::lean_box(0);
                                    v_isShared_5847_ = v_isSharedCheck_5851_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_5823_);
                            leanh::lean_dec(v_a_5821_);
                            leanh::lean_dec_ref(v___x_5819_);
                            leanh::lean_dec_ref(v_e_5792_);
                            return v___x_5824_;
                        }
                    } else {
                        leanh::lean_dec(v_a_5821_);
                        leanh::lean_dec_ref(v___x_5819_);
                        leanh::lean_dec_ref(v_e_5792_);
                        v_a_5852_ = leanh::lean_ctor_get(v___x_5822_, 0);
                        v_isSharedCheck_5859_ =
                            (!leanh::lean_is_exclusive(v___x_5822_)) as u8;
                        if v_isSharedCheck_5859_ == 0 {
                            v___x_5854_ = v___x_5822_;
                            v_isShared_5855_ = v_isSharedCheck_5859_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5852_);
                            leanh::lean_dec(v___x_5822_);
                            v___x_5854_ = leanh::lean_box(0);
                            v_isShared_5855_ = v_isSharedCheck_5859_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5819_);
                    leanh::lean_dec_ref(v_e_5792_);
                    leanh::lean_dec_ref(v_00_u03c3s_5790_);
                    v_a_5860_ = leanh::lean_ctor_get(v___x_5820_, 0);
                    v_isSharedCheck_5867_ = (!leanh::lean_is_exclusive(v___x_5820_)) as u8;
                    if v_isSharedCheck_5867_ == 0 {
                        v___x_5862_ = v___x_5820_;
                        v_isShared_5863_ = v_isSharedCheck_5867_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5860_);
                        leanh::lean_dec(v___x_5820_);
                        v___x_5862_ = leanh::lean_box(0);
                        v_isShared_5863_ = v_isSharedCheck_5867_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_5836_ = leanh::lean_ctor_get(v_a_5832_, 1);
                leanh::lean_inc(v_snd_5836_);
                leanh::lean_dec(v_a_5832_);
                v_snd_5837_ = leanh::lean_ctor_get(v_snd_5836_, 1);
                leanh::lean_inc(v_snd_5837_);
                leanh::lean_dec(v_snd_5836_);
                v_snd_5838_ = leanh::lean_ctor_get(v_snd_5837_, 1);
                leanh::lean_inc(v_snd_5838_);
                leanh::lean_dec(v_snd_5837_);
                v_fst_5839_ = leanh::lean_ctor_get(v_snd_5838_, 0);
                leanh::lean_inc(v_fst_5839_);
                leanh::lean_dec(v_snd_5838_);
                if v_isShared_5835_ == 0 {
                    leanh::lean_ctor_set(v___x_5834_, 0, v_fst_5839_);
                    v___x_5841_ = v___x_5834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_fst_5839_);
                    v___x_5841_ = v_reuseFailAlloc_5842_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5841_;
            }
            7 => {
                if v_isShared_5847_ == 0 {
                    v___x_5849_ = v___x_5846_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
                    v___x_5849_ = v_reuseFailAlloc_5850_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5849_;
            }
            9 => {
                if v_isShared_5855_ == 0 {
                    v___x_5857_ = v___x_5854_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5858_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
                    v___x_5857_ = v_reuseFailAlloc_5858_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5857_;
            }
            11 => {
                if v_isShared_5863_ == 0 {
                    v___x_5865_ = v___x_5862_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
                    v___x_5865_ = v_reuseFailAlloc_5866_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed(
    mut v___x_5875_: *mut leanh::LeanObject,
    mut v___x_5876_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5877_: *mut leanh::LeanObject,
    mut v_xs_5878_: *mut leanh::LeanObject,
    mut v_e_5879_: *mut leanh::LeanObject,
    mut v___y_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5010__boxed_5885_: u8 = 0;
    let mut v_res_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5010__boxed_5885_ = (leanh::lean_unbox(v___x_5876_) as u8);
    v_res_5886_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(
        v___x_5875_,
        v___x_5010__boxed_5885_,
        v_00_u03c3s_5877_,
        v_xs_5878_,
        v_e_5879_,
        v___y_5880_,
        v___y_5881_,
        v___y_5882_,
        v___y_5883_,
    );
    leanh::lean_dec(v___y_5883_);
    leanh::lean_dec_ref(v___y_5882_);
    leanh::lean_dec(v___y_5881_);
    leanh::lean_dec_ref(v_xs_5878_);
    return v_res_5886_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
    mut v_xs_5887_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5888_: *mut leanh::LeanObject,
    mut v_e_5889_: *mut leanh::LeanObject,
    mut v_a_5890_: *mut leanh::LeanObject,
    mut v_a_5891_: *mut leanh::LeanObject,
    mut v_a_5892_: *mut leanh::LeanObject,
    mut v_a_5893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: u8 = 0;
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: u8 = 0;
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5895_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
    v___x_5896_ = lean_array_get_size(v_xs_5887_);
    v___x_5897_ = leanh::lean_unsigned_to_nat(0);
    v___x_5898_ = lean_nat_dec_eq(v___x_5896_, v___x_5897_);
    v___x_5899_ = leanh::lean_box((v___x_5898_) as usize);
    v___f_5900_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    leanh::lean_closure_set(v___f_5900_, 0, v___x_5895_);
    leanh::lean_closure_set(v___f_5900_, 1, v___x_5899_);
    leanh::lean_closure_set(v___f_5900_, 2, v_00_u03c3s_5888_);
    leanh::lean_closure_set(v___f_5900_, 3, v_xs_5887_);
    leanh::lean_closure_set(v___f_5900_, 4, v_e_5889_);
    v___x_5901_ = 0;
    v___x_5902_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_5900_, v___x_5901_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
    return v___x_5902_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(
    mut v_xs_5903_: *mut leanh::LeanObject,
    mut v_00_u03c3s_5904_: *mut leanh::LeanObject,
    mut v_e_5905_: *mut leanh::LeanObject,
    mut v_a_5906_: *mut leanh::LeanObject,
    mut v_a_5907_: *mut leanh::LeanObject,
    mut v_a_5908_: *mut leanh::LeanObject,
    mut v_a_5909_: *mut leanh::LeanObject,
    mut v_a_5910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5911_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
        v_xs_5903_,
        v_00_u03c3s_5904_,
        v_e_5905_,
        v_a_5906_,
        v_a_5907_,
        v_a_5908_,
        v_a_5909_,
    );
    leanh::lean_dec(v_a_5909_);
    leanh::lean_dec_ref(v_a_5908_);
    leanh::lean_dec(v_a_5907_);
    leanh::lean_dec_ref(v_a_5906_);
    return v_res_5911_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(
    mut v_a_5912_: *mut leanh::LeanObject,
    mut v_xs_5913_: *mut leanh::LeanObject,
    mut v_inst_5914_: *mut leanh::LeanObject,
    mut v_a_5915_: *mut leanh::LeanObject,
    mut v___y_5916_: *mut leanh::LeanObject,
    mut v___y_5917_: *mut leanh::LeanObject,
    mut v___y_5918_: *mut leanh::LeanObject,
    mut v___y_5919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5921_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_5912_, v_xs_5913_, v_a_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
    return v___x_5921_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(
    mut v_a_5922_: *mut leanh::LeanObject,
    mut v_xs_5923_: *mut leanh::LeanObject,
    mut v_inst_5924_: *mut leanh::LeanObject,
    mut v_a_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
    mut v___y_5927_: *mut leanh::LeanObject,
    mut v___y_5928_: *mut leanh::LeanObject,
    mut v___y_5929_: *mut leanh::LeanObject,
    mut v___y_5930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5931_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_5922_, v_xs_5923_, v_inst_5924_, v_a_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
    leanh::lean_dec(v___y_5929_);
    leanh::lean_dec_ref(v___y_5928_);
    leanh::lean_dec(v___y_5927_);
    leanh::lean_dec_ref(v___y_5926_);
    leanh::lean_dec_ref(v_xs_5923_);
    return v_res_5931_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5933_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0;
    v___x_5934_ = l_Lean_stringToMessageData(v___x_5933_);
    return v___x_5934_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(
    mut v_a_5948_: *mut leanh::LeanObject,
    mut v___x_5949_: *mut leanh::LeanObject,
    mut v___x_5950_: u8,
    mut v___x_5951_: *mut leanh::LeanObject,
    mut v_proof_5952_: *mut leanh::LeanObject,
    mut v_prio_5953_: *mut leanh::LeanObject,
    mut v___y_5954_: *mut leanh::LeanObject,
    mut v___y_5955_: *mut leanh::LeanObject,
    mut v___y_5956_: *mut leanh::LeanObject,
    mut v___y_5957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5961_: u8 = 0;
    let mut v_zetaDeltaSet_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5968_: u8 = 0;
    let mut v_inTypeClassResolution_5969_: u8 = 0;
    let mut v_cacheInferType_5970_: u8 = 0;
    let mut v___x_5971_: u64 = 0;
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5980_: u8 = 0;
    let mut v_snd_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: u8 = 0;
    let mut v_arg_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut v_arg_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: u8 = 0;
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: u8 = 0;
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: u8 = 0;
    let mut v_arg_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: u8 = 0;
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: u8 = 0;
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: u8 = 0;
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6037_: u8 = 0;
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6042_: u8 = 0;
    let mut v_a_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6046_: u8 = 0;
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6050_: u8 = 0;
    let mut v_a_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v_reuseFailAlloc_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6063_: u8 = 0;
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6067_: u8 = 0;
    let mut v_a_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6071_: u8 = 0;
    let mut v___x_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut v_isSharedCheck_6076_: u8 = 0;
    let mut v_unused_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6078_: u8 = 0;
    let mut v_a_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5959_ = l_Lean_Meta_simpGlobalConfig;
                v_config_5960_ = leanh::lean_ctor_get(v___x_5959_, 0);
                v_trackZetaDelta_5961_ = leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5962_ = leanh::lean_ctor_get(v___y_5954_, 1);
                v_lctx_5963_ = leanh::lean_ctor_get(v___y_5954_, 2);
                v_localInstances_5964_ = leanh::lean_ctor_get(v___y_5954_, 3);
                v_defEqCtx_x3f_5965_ = leanh::lean_ctor_get(v___y_5954_, 4);
                v_synthPendingDepth_5966_ = leanh::lean_ctor_get(v___y_5954_, 5);
                v_canUnfold_x3f_5967_ = leanh::lean_ctor_get(v___y_5954_, 6);
                v_univApprox_5968_ = leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5969_ = leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5970_ = leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_5960_);
                leanh::lean_inc_ref(v_config_5960_);
                v___x_5972_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5972_, 0, v_config_5960_);
                leanh::lean_ctor_set_uint64(
                    v___x_5972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5971_,
                );
                leanh::lean_inc(v_canUnfold_x3f_5967_);
                leanh::lean_inc(v_synthPendingDepth_5966_);
                leanh::lean_inc(v_defEqCtx_x3f_5965_);
                leanh::lean_inc_ref(v_localInstances_5964_);
                leanh::lean_inc_ref(v_lctx_5963_);
                leanh::lean_inc(v_zetaDeltaSet_5962_);
                v___x_5973_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_5973_, 0, v___x_5972_);
                leanh::lean_ctor_set(v___x_5973_, 1, v_zetaDeltaSet_5962_);
                leanh::lean_ctor_set(v___x_5973_, 2, v_lctx_5963_);
                leanh::lean_ctor_set(v___x_5973_, 3, v_localInstances_5964_);
                leanh::lean_ctor_set(v___x_5973_, 4, v_defEqCtx_x3f_5965_);
                leanh::lean_ctor_set(v___x_5973_, 5, v_synthPendingDepth_5966_);
                leanh::lean_ctor_set(v___x_5973_, 6, v_canUnfold_x3f_5967_);
                leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5961_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5968_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5969_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5970_,
                );
                v___x_5974_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_a_5948_,
                    v___x_5949_,
                    v___x_5950_,
                    v___x_5973_,
                    v___y_5955_,
                    v___y_5956_,
                    v___y_5957_,
                );
                leanh::lean_dec_ref_known(v___x_5973_, 7);
                if leanh::lean_obj_tag(v___x_5974_) == 0 {
                    v_a_5975_ = leanh::lean_ctor_get(v___x_5974_, 0);
                    leanh::lean_inc(v_a_5975_);
                    leanh::lean_dec_ref_known(v___x_5974_, 1);
                    v_snd_5976_ = leanh::lean_ctor_get(v_a_5975_, 1);
                    v_fst_5977_ = leanh::lean_ctor_get(v_a_5975_, 0);
                    v_isSharedCheck_6078_ = (!leanh::lean_is_exclusive(v_a_5975_)) as u8;
                    if v_isSharedCheck_6078_ == 0 {
                        v___x_5979_ = v_a_5975_;
                        v_isShared_5980_ = v_isSharedCheck_6078_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5976_);
                        leanh::lean_inc(v_fst_5977_);
                        leanh::lean_dec(v_a_5975_);
                        v___x_5979_ = leanh::lean_box(0);
                        v_isShared_5980_ = v_isSharedCheck_6078_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_prio_5953_);
                    leanh::lean_dec_ref(v_proof_5952_);
                    v_a_6079_ = leanh::lean_ctor_get(v___x_5974_, 0);
                    v_isSharedCheck_6086_ = (!leanh::lean_is_exclusive(v___x_5974_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6081_ = v___x_5974_;
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6079_);
                        leanh::lean_dec(v___x_5974_);
                        v___x_6081_ = leanh::lean_box(0);
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5981_ = leanh::lean_ctor_get(v_snd_5976_, 1);
                v_isSharedCheck_6076_ = (!leanh::lean_is_exclusive(v_snd_5976_)) as u8;
                if v_isSharedCheck_6076_ == 0 {
                    v_unused_6077_ = leanh::lean_ctor_get(v_snd_5976_, 0);
                    leanh::lean_dec(v_unused_6077_);
                    v___x_5983_ = v_snd_5976_;
                    v_isShared_5984_ = v_isSharedCheck_6076_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5981_);
                    leanh::lean_dec(v_snd_5976_);
                    v___x_5983_ = leanh::lean_box(0);
                    v_isShared_5984_ = v_isSharedCheck_6076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5985_ = l_Lean_Meta_whnfR(
                    v_snd_5981_,
                    v___y_5954_,
                    v___y_5955_,
                    v___y_5956_,
                    v___y_5957_,
                );
                if leanh::lean_obj_tag(v___x_5985_) == 0 {
                    v_a_5986_ = leanh::lean_ctor_get(v___x_5985_, 0);
                    leanh::lean_inc_n(v_a_5986_, 2);
                    leanh::lean_dec_ref_known(v___x_5985_, 1);
                    v___x_5998_ = l_Lean_Expr_cleanupAnnotations(v_a_5986_);
                    v___x_5999_ = l_Lean_Expr_isApp(v___x_5998_);
                    if v___x_5999_ == 0 {
                        leanh::lean_dec_ref(v___x_5998_);
                        leanh::lean_del_object(v___x_5979_);
                        leanh::lean_dec(v_fst_5977_);
                        leanh::lean_dec(v_prio_5953_);
                        leanh::lean_dec_ref(v_proof_5952_);
                        v___y_5988_ = v___y_5954_;
                        v___y_5989_ = v___y_5955_;
                        v___y_5990_ = v___y_5956_;
                        v___y_5991_ = v___y_5957_;
                        state = 3;
                        continue;
                    } else {
                        v___x_6000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5998_);
                        v___x_6001_ = l_Lean_Expr_isApp(v___x_6000_);
                        if v___x_6001_ == 0 {
                            leanh::lean_dec_ref(v___x_6000_);
                            leanh::lean_del_object(v___x_5979_);
                            leanh::lean_dec(v_fst_5977_);
                            leanh::lean_dec(v_prio_5953_);
                            leanh::lean_dec_ref(v_proof_5952_);
                            v___y_5988_ = v___y_5954_;
                            v___y_5989_ = v___y_5955_;
                            v___y_5990_ = v___y_5956_;
                            v___y_5991_ = v___y_5957_;
                            state = 3;
                            continue;
                        } else {
                            v_arg_6002_ = leanh::lean_ctor_get(v___x_6000_, 1);
                            leanh::lean_inc_ref(v_arg_6002_);
                            v___x_6003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6000_);
                            v___x_6004_ = l_Lean_Expr_isApp(v___x_6003_);
                            if v___x_6004_ == 0 {
                                leanh::lean_dec_ref(v___x_6003_);
                                leanh::lean_dec_ref(v_arg_6002_);
                                leanh::lean_del_object(v___x_5979_);
                                leanh::lean_dec(v_fst_5977_);
                                leanh::lean_dec(v_prio_5953_);
                                leanh::lean_dec_ref(v_proof_5952_);
                                v___y_5988_ = v___y_5954_;
                                v___y_5989_ = v___y_5955_;
                                v___y_5990_ = v___y_5956_;
                                v___y_5991_ = v___y_5957_;
                                state = 3;
                                continue;
                            } else {
                                v_arg_6005_ = leanh::lean_ctor_get(v___x_6003_, 1);
                                leanh::lean_inc_ref(v_arg_6005_);
                                v___x_6006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6003_);
                                v___x_6007_ = l_Lean_Expr_isApp(v___x_6006_);
                                if v___x_6007_ == 0 {
                                    leanh::lean_dec_ref(v___x_6006_);
                                    leanh::lean_dec_ref(v_arg_6005_);
                                    leanh::lean_dec_ref(v_arg_6002_);
                                    leanh::lean_del_object(v___x_5979_);
                                    leanh::lean_dec(v_fst_5977_);
                                    leanh::lean_dec(v_prio_5953_);
                                    leanh::lean_dec_ref(v_proof_5952_);
                                    v___y_5988_ = v___y_5954_;
                                    v___y_5989_ = v___y_5955_;
                                    v___y_5990_ = v___y_5956_;
                                    v___y_5991_ = v___y_5957_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_6008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6006_);
                                    v___x_6009_ = l_Lean_Expr_isApp(v___x_6008_);
                                    if v___x_6009_ == 0 {
                                        leanh::lean_dec_ref(v___x_6008_);
                                        leanh::lean_dec_ref(v_arg_6005_);
                                        leanh::lean_dec_ref(v_arg_6002_);
                                        leanh::lean_del_object(v___x_5979_);
                                        leanh::lean_dec(v_fst_5977_);
                                        leanh::lean_dec(v_prio_5953_);
                                        leanh::lean_dec_ref(v_proof_5952_);
                                        v___y_5988_ = v___y_5954_;
                                        v___y_5989_ = v___y_5955_;
                                        v___y_5990_ = v___y_5956_;
                                        v___y_5991_ = v___y_5957_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_6010_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_6008_);
                                        v___x_6011_ = l_Lean_Expr_isApp(v___x_6010_);
                                        if v___x_6011_ == 0 {
                                            leanh::lean_dec_ref(v___x_6010_);
                                            leanh::lean_dec_ref(v_arg_6005_);
                                            leanh::lean_dec_ref(v_arg_6002_);
                                            leanh::lean_del_object(v___x_5979_);
                                            leanh::lean_dec(v_fst_5977_);
                                            leanh::lean_dec(v_prio_5953_);
                                            leanh::lean_dec_ref(v_proof_5952_);
                                            v___y_5988_ = v___y_5954_;
                                            v___y_5989_ = v___y_5955_;
                                            v___y_5990_ = v___y_5956_;
                                            v___y_5991_ = v___y_5957_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_arg_6012_ =
                                                leanh::lean_ctor_get(v___x_6010_, 1);
                                            leanh::lean_inc_ref(v_arg_6012_);
                                            v___x_6013_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_6010_);
                                            v___x_6014_ = l_Lean_Expr_isApp(v___x_6013_);
                                            if v___x_6014_ == 0 {
                                                leanh::lean_dec_ref(v___x_6013_);
                                                leanh::lean_dec_ref(v_arg_6012_);
                                                leanh::lean_dec_ref(v_arg_6005_);
                                                leanh::lean_dec_ref(v_arg_6002_);
                                                leanh::lean_del_object(v___x_5979_);
                                                leanh::lean_dec(v_fst_5977_);
                                                leanh::lean_dec(v_prio_5953_);
                                                leanh::lean_dec_ref(v_proof_5952_);
                                                v___y_5988_ = v___y_5954_;
                                                v___y_5989_ = v___y_5955_;
                                                v___y_5990_ = v___y_5956_;
                                                v___y_5991_ = v___y_5957_;
                                                state = 3;
                                                continue;
                                            } else {
                                                v___x_6015_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_6013_);
                                                v___x_6016_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4;
                                                v___x_6017_ =
                                                    l_Lean_Expr_isConstOf(v___x_6015_, v___x_6016_);
                                                if v___x_6017_ == 0 {
                                                    leanh::lean_dec_ref(v___x_6015_);
                                                    leanh::lean_dec_ref(v_arg_6012_);
                                                    leanh::lean_dec_ref(v_arg_6005_);
                                                    leanh::lean_dec_ref(v_arg_6002_);
                                                    leanh::lean_del_object(v___x_5979_);
                                                    leanh::lean_dec(v_fst_5977_);
                                                    leanh::lean_dec(v_prio_5953_);
                                                    leanh::lean_dec_ref(v_proof_5952_);
                                                    v___y_5988_ = v___y_5954_;
                                                    v___y_5989_ = v___y_5955_;
                                                    v___y_5990_ = v___y_5956_;
                                                    v___y_5991_ = v___y_5957_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v_a_5986_);
                                                    leanh::lean_del_object(v___x_5983_);
                                                    v___x_6018_ = 0;
                                                    leanh::lean_inc_ref(v_arg_6005_);
                                                    v___x_6019_ = l_Lean_Meta_DiscrTree_mkPath(
                                                        v_arg_6005_,
                                                        v___x_6018_,
                                                        v___y_5954_,
                                                        v___y_5955_,
                                                        v___y_5956_,
                                                        v___y_5957_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_6019_) == 0
                                                    {
                                                        v_a_6020_ = leanh::lean_ctor_get(
                                                            v___x_6019_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_6020_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_6019_,
                                                            1,
                                                        );
                                                        v___x_6021_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7;
                                                        v___x_6022_ = l_Lean_Expr_constLevels_x21(
                                                            v___x_6015_,
                                                        );
                                                        leanh::lean_dec_ref(v___x_6015_);
                                                        v___x_6023_ =
                                                            leanh::lean_unsigned_to_nat(0);
                                                        v___x_6024_ =
                                                            l_List_get_x21Internal___redArg(
                                                                v___x_5951_,
                                                                v___x_6022_,
                                                                v___x_6023_,
                                                            );
                                                        leanh::lean_dec(v___x_6022_);
                                                        v___x_6025_ = leanh::lean_box(0);
                                                        if v_isShared_5980_ == 0 {
                                                            leanh::lean_ctor_set_tag(
                                                                v___x_5979_,
                                                                1,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_5979_,
                                                                1,
                                                                v___x_6025_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_5979_,
                                                                0,
                                                                v___x_6024_,
                                                            );
                                                            v___x_6027_ = v___x_5979_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_6059_ =
                                                                leanh::lean_alloc_ctor(
                                                                    1,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_6059_,
                                                                0,
                                                                v___x_6024_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_6059_,
                                                                1,
                                                                v___x_6025_,
                                                            );
                                                            v___x_6027_ = v_reuseFailAlloc_6059_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_6015_);
                                                        leanh::lean_dec_ref(v_arg_6012_);
                                                        leanh::lean_dec_ref(v_arg_6005_);
                                                        leanh::lean_dec_ref(v_arg_6002_);
                                                        leanh::lean_del_object(v___x_5979_);
                                                        leanh::lean_dec(v_fst_5977_);
                                                        leanh::lean_dec(v_prio_5953_);
                                                        leanh::lean_dec_ref(v_proof_5952_);
                                                        v_a_6060_ = leanh::lean_ctor_get(
                                                            v___x_6019_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_6067_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_6019_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_6067_ == 0 {
                                                            v___x_6062_ = v___x_6019_;
                                                            v_isShared_6063_ =
                                                                v_isSharedCheck_6067_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_6060_);
                                                            leanh::lean_dec(v___x_6019_);
                                                            v___x_6062_ = leanh::lean_box(0);
                                                            v_isShared_6063_ =
                                                                v_isSharedCheck_6067_;
                                                            state = 12;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5983_);
                    leanh::lean_del_object(v___x_5979_);
                    leanh::lean_dec(v_fst_5977_);
                    leanh::lean_dec(v_prio_5953_);
                    leanh::lean_dec_ref(v_proof_5952_);
                    v_a_6068_ = leanh::lean_ctor_get(v___x_5985_, 0);
                    v_isSharedCheck_6075_ = (!leanh::lean_is_exclusive(v___x_5985_)) as u8;
                    if v_isSharedCheck_6075_ == 0 {
                        v___x_6070_ = v___x_5985_;
                        v_isShared_6071_ = v_isSharedCheck_6075_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6068_);
                        leanh::lean_dec(v___x_5985_);
                        v___x_6070_ = leanh::lean_box(0);
                        v_isShared_6071_ = v_isSharedCheck_6075_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5992_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
                v___x_5993_ = l_Lean_indentExpr(v_a_5986_);
                if v_isShared_5984_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5983_, 7);
                    leanh::lean_ctor_set(v___x_5983_, 1, v___x_5993_);
                    leanh::lean_ctor_set(v___x_5983_, 0, v___x_5992_);
                    v___x_5995_ = v___x_5983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5997_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5997_, 0, v___x_5992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5997_, 1, v___x_5993_);
                    v___x_5995_ = v_reuseFailAlloc_5997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5996_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_5995_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
                return v___x_5996_;
            }
            5 => {
                v___x_6028_ = l_Lean_mkConst(v___x_6021_, v___x_6027_);
                v___x_6029_ = l_Lean_Expr_app___override(v___x_6028_, v_arg_6012_);
                leanh::lean_inc(v_fst_5977_);
                v___x_6030_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
                    v_fst_5977_,
                    v___x_6029_,
                    v_arg_6002_,
                    v___y_5954_,
                    v___y_5955_,
                    v___y_5956_,
                    v___y_5957_,
                );
                if leanh::lean_obj_tag(v___x_6030_) == 0 {
                    v_a_6031_ = leanh::lean_ctor_get(v___x_6030_, 0);
                    leanh::lean_inc(v_a_6031_);
                    leanh::lean_dec_ref_known(v___x_6030_, 1);
                    v___x_6032_ = 1;
                    v___x_6033_ = l_Lean_Meta_mkForallFVars(
                        v_fst_5977_,
                        v_arg_6005_,
                        v___x_6018_,
                        v___x_6017_,
                        v___x_6017_,
                        v___x_6032_,
                        v___y_5954_,
                        v___y_5955_,
                        v___y_5956_,
                        v___y_5957_,
                    );
                    leanh::lean_dec(v_fst_5977_);
                    if leanh::lean_obj_tag(v___x_6033_) == 0 {
                        v_a_6034_ = leanh::lean_ctor_get(v___x_6033_, 0);
                        v_isSharedCheck_6042_ =
                            (!leanh::lean_is_exclusive(v___x_6033_)) as u8;
                        if v_isSharedCheck_6042_ == 0 {
                            v___x_6036_ = v___x_6033_;
                            v_isShared_6037_ = v_isSharedCheck_6042_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6034_);
                            leanh::lean_dec(v___x_6033_);
                            v___x_6036_ = leanh::lean_box(0);
                            v_isShared_6037_ = v_isSharedCheck_6042_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6031_);
                        leanh::lean_dec(v_a_6020_);
                        leanh::lean_dec(v_prio_5953_);
                        leanh::lean_dec_ref(v_proof_5952_);
                        v_a_6043_ = leanh::lean_ctor_get(v___x_6033_, 0);
                        v_isSharedCheck_6050_ =
                            (!leanh::lean_is_exclusive(v___x_6033_)) as u8;
                        if v_isSharedCheck_6050_ == 0 {
                            v___x_6045_ = v___x_6033_;
                            v_isShared_6046_ = v_isSharedCheck_6050_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6043_);
                            leanh::lean_dec(v___x_6033_);
                            v___x_6045_ = leanh::lean_box(0);
                            v_isShared_6046_ = v_isSharedCheck_6050_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6020_);
                    leanh::lean_dec_ref(v_arg_6005_);
                    leanh::lean_dec(v_fst_5977_);
                    leanh::lean_dec(v_prio_5953_);
                    leanh::lean_dec_ref(v_proof_5952_);
                    v_a_6051_ = leanh::lean_ctor_get(v___x_6030_, 0);
                    v_isSharedCheck_6058_ = (!leanh::lean_is_exclusive(v___x_6030_)) as u8;
                    if v_isSharedCheck_6058_ == 0 {
                        v___x_6053_ = v___x_6030_;
                        v_isShared_6054_ = v_isSharedCheck_6058_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6051_);
                        leanh::lean_dec(v___x_6030_);
                        v___x_6053_ = leanh::lean_box(0);
                        v_isShared_6054_ = v_isSharedCheck_6058_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6038_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6038_, 0, v_a_6020_);
                leanh::lean_ctor_set(v___x_6038_, 1, v_a_6034_);
                leanh::lean_ctor_set(v___x_6038_, 2, v_proof_5952_);
                leanh::lean_ctor_set(v___x_6038_, 3, v_a_6031_);
                leanh::lean_ctor_set(v___x_6038_, 4, v_prio_5953_);
                if v_isShared_6037_ == 0 {
                    leanh::lean_ctor_set(v___x_6036_, 0, v___x_6038_);
                    v___x_6040_ = v___x_6036_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6041_, 0, v___x_6038_);
                    v___x_6040_ = v_reuseFailAlloc_6041_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6040_;
            }
            8 => {
                if v_isShared_6046_ == 0 {
                    v___x_6048_ = v___x_6045_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6049_, 0, v_a_6043_);
                    v___x_6048_ = v_reuseFailAlloc_6049_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6048_;
            }
            10 => {
                if v_isShared_6054_ == 0 {
                    v___x_6056_ = v___x_6053_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
                    v___x_6056_ = v_reuseFailAlloc_6057_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6056_;
            }
            12 => {
                if v_isShared_6063_ == 0 {
                    v___x_6065_ = v___x_6062_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6066_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
                    v___x_6065_ = v_reuseFailAlloc_6066_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6065_;
            }
            14 => {
                if v_isShared_6071_ == 0 {
                    v___x_6073_ = v___x_6070_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6068_);
                    v___x_6073_ = v_reuseFailAlloc_6074_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6073_;
            }
            16 => {
                if v_isShared_6082_ == 0 {
                    v___x_6084_ = v___x_6081_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
                    v___x_6084_ = v_reuseFailAlloc_6085_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed(
    mut v_a_6087_: *mut leanh::LeanObject,
    mut v___x_6088_: *mut leanh::LeanObject,
    mut v___x_6089_: *mut leanh::LeanObject,
    mut v___x_6090_: *mut leanh::LeanObject,
    mut v_proof_6091_: *mut leanh::LeanObject,
    mut v_prio_6092_: *mut leanh::LeanObject,
    mut v___y_6093_: *mut leanh::LeanObject,
    mut v___y_6094_: *mut leanh::LeanObject,
    mut v___y_6095_: *mut leanh::LeanObject,
    mut v___y_6096_: *mut leanh::LeanObject,
    mut v___y_6097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3664__boxed_6098_: u8 = 0;
    let mut v_res_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3664__boxed_6098_ = (leanh::lean_unbox(v___x_6089_) as u8);
    v_res_6099_ =
        l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(
            v_a_6087_,
            v___x_6088_,
            v___x_3664__boxed_6098_,
            v___x_6090_,
            v_proof_6091_,
            v_prio_6092_,
            v___y_6093_,
            v___y_6094_,
            v___y_6095_,
            v___y_6096_,
        );
    leanh::lean_dec(v___y_6096_);
    leanh::lean_dec_ref(v___y_6095_);
    leanh::lean_dec(v___y_6094_);
    leanh::lean_dec_ref(v___y_6093_);
    leanh::lean_dec(v___x_6090_);
    return v_res_6099_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6101_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0;
    v___x_6102_ = l_Lean_stringToMessageData(v___x_6101_);
    return v___x_6102_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(
    mut v_type_6103_: *mut leanh::LeanObject,
    mut v_proof_6104_: *mut leanh::LeanObject,
    mut v_prio_6105_: *mut leanh::LeanObject,
    mut v_a_6106_: *mut leanh::LeanObject,
    mut v_a_6107_: *mut leanh::LeanObject,
    mut v_a_6108_: *mut leanh::LeanObject,
    mut v_a_6109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: u8 = 0;
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: u8 = 0;
    let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: u8 = 0;
    let mut v___x_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6135_: u8 = 0;
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6139_: u8 = 0;
    let mut v_a_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6111_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_6103_, v_a_6107_);
                v_a_6112_ = leanh::lean_ctor_get(v___x_6111_, 0);
                leanh::lean_inc_n(v_a_6112_, 2);
                leanh::lean_dec_ref(v___x_6111_);
                v___x_6113_ =
                    l_Lean_Meta_isProp(v_a_6112_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_);
                if leanh::lean_obj_tag(v___x_6113_) == 0 {
                    v_a_6114_ = leanh::lean_ctor_get(v___x_6113_, 0);
                    leanh::lean_inc(v_a_6114_);
                    leanh::lean_dec_ref_known(v___x_6113_, 1);
                    v___x_6115_ = leanh::lean_box(0);
                    v___x_6127_ = (leanh::lean_unbox(v_a_6114_) as u8);
                    leanh::lean_dec(v_a_6114_);
                    if v___x_6127_ == 0 {
                        leanh::lean_dec(v_prio_6105_);
                        leanh::lean_dec_ref(v_proof_6104_);
                        v___x_6128_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
                        v___x_6129_ = l_Lean_indentExpr(v_a_6112_);
                        v___x_6130_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6130_, 0, v___x_6128_);
                        leanh::lean_ctor_set(v___x_6130_, 1, v___x_6129_);
                        v___x_6131_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_6130_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_);
                        v_a_6132_ = leanh::lean_ctor_get(v___x_6131_, 0);
                        v_isSharedCheck_6139_ =
                            (!leanh::lean_is_exclusive(v___x_6131_)) as u8;
                        if v_isSharedCheck_6139_ == 0 {
                            v___x_6134_ = v___x_6131_;
                            v_isShared_6135_ = v_isSharedCheck_6139_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6132_);
                            leanh::lean_dec(v___x_6131_);
                            v___x_6134_ = leanh::lean_box(0);
                            v_isShared_6135_ = v_isSharedCheck_6139_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_6117_ = v_a_6106_;
                        v___y_6118_ = v_a_6107_;
                        v___y_6119_ = v_a_6108_;
                        v___y_6120_ = v_a_6109_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6112_);
                    leanh::lean_dec(v_prio_6105_);
                    leanh::lean_dec_ref(v_proof_6104_);
                    v_a_6140_ = leanh::lean_ctor_get(v___x_6113_, 0);
                    v_isSharedCheck_6147_ = (!leanh::lean_is_exclusive(v___x_6113_)) as u8;
                    if v_isSharedCheck_6147_ == 0 {
                        v___x_6142_ = v___x_6113_;
                        v_isShared_6143_ = v_isSharedCheck_6147_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6140_);
                        leanh::lean_dec(v___x_6113_);
                        v___x_6142_ = leanh::lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6147_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6121_ = leanh::lean_box(0);
                v___x_6122_ = 0;
                v___x_6123_ = leanh::lean_box((v___x_6122_) as usize);
                v___f_6124_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                leanh::lean_closure_set(v___f_6124_, 0, v_a_6112_);
                leanh::lean_closure_set(v___f_6124_, 1, v___x_6121_);
                leanh::lean_closure_set(v___f_6124_, 2, v___x_6123_);
                leanh::lean_closure_set(v___f_6124_, 3, v___x_6115_);
                leanh::lean_closure_set(v___f_6124_, 4, v_proof_6104_);
                leanh::lean_closure_set(v___f_6124_, 5, v_prio_6105_);
                v___x_6125_ = 0;
                v___x_6126_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_6124_, v___x_6125_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
                return v___x_6126_;
            }
            2 => {
                if v_isShared_6135_ == 0 {
                    v___x_6137_ = v___x_6134_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6138_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6138_, 0, v_a_6132_);
                    v___x_6137_ = v_reuseFailAlloc_6138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6137_;
            }
            4 => {
                if v_isShared_6143_ == 0 {
                    v___x_6145_ = v___x_6142_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_a_6140_);
                    v___x_6145_ = v_reuseFailAlloc_6146_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___boxed(
    mut v_type_6148_: *mut leanh::LeanObject,
    mut v_proof_6149_: *mut leanh::LeanObject,
    mut v_prio_6150_: *mut leanh::LeanObject,
    mut v_a_6151_: *mut leanh::LeanObject,
    mut v_a_6152_: *mut leanh::LeanObject,
    mut v_a_6153_: *mut leanh::LeanObject,
    mut v_a_6154_: *mut leanh::LeanObject,
    mut v_a_6155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6156_ =
        l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(
            v_type_6148_,
            v_proof_6149_,
            v_prio_6150_,
            v_a_6151_,
            v_a_6152_,
            v_a_6153_,
            v_a_6154_,
        );
    leanh::lean_dec(v_a_6154_);
    leanh::lean_dec_ref(v_a_6153_);
    leanh::lean_dec(v_a_6152_);
    leanh::lean_dec_ref(v_a_6151_);
    return v_res_6156_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(
    mut v_declName_6157_: *mut leanh::LeanObject,
    mut v_prio_6158_: *mut leanh::LeanObject,
    mut v_a_6159_: *mut leanh::LeanObject,
    mut v_a_6160_: *mut leanh::LeanObject,
    mut v_a_6161_: *mut leanh::LeanObject,
    mut v_a_6162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut v_a_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_6157_);
                v___x_6164_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_6157_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
                if leanh::lean_obj_tag(v___x_6164_) == 0 {
                    v_a_6165_ = leanh::lean_ctor_get(v___x_6164_, 0);
                    leanh::lean_inc(v_a_6165_);
                    leanh::lean_dec_ref_known(v___x_6164_, 1);
                    v___x_6166_ = l_Lean_ConstantInfo_levelParams(v_a_6165_);
                    leanh::lean_dec(v_a_6165_);
                    v___x_6167_ = leanh::lean_box(0);
                    v___x_6168_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_6166_, v___x_6167_);
                    leanh::lean_inc(v_declName_6157_);
                    v___x_6169_ = l_Lean_mkConst(v_declName_6157_, v___x_6168_);
                    leanh::lean_inc(v_a_6162_);
                    leanh::lean_inc_ref(v_a_6161_);
                    leanh::lean_inc(v_a_6160_);
                    leanh::lean_inc_ref(v_a_6159_);
                    v___x_6170_ =
                        lean_infer_type(v___x_6169_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
                    if leanh::lean_obj_tag(v___x_6170_) == 0 {
                        v_a_6171_ = leanh::lean_ctor_get(v___x_6170_, 0);
                        leanh::lean_inc(v_a_6171_);
                        leanh::lean_dec_ref_known(v___x_6170_, 1);
                        v___x_6172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6172_, 0, v_declName_6157_);
                        v___x_6173_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_6171_, v___x_6172_, v_prio_6158_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
                        return v___x_6173_;
                    } else {
                        leanh::lean_dec(v_prio_6158_);
                        leanh::lean_dec(v_declName_6157_);
                        v_a_6174_ = leanh::lean_ctor_get(v___x_6170_, 0);
                        v_isSharedCheck_6181_ =
                            (!leanh::lean_is_exclusive(v___x_6170_)) as u8;
                        if v_isSharedCheck_6181_ == 0 {
                            v___x_6176_ = v___x_6170_;
                            v_isShared_6177_ = v_isSharedCheck_6181_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6174_);
                            leanh::lean_dec(v___x_6170_);
                            v___x_6176_ = leanh::lean_box(0);
                            v_isShared_6177_ = v_isSharedCheck_6181_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_prio_6158_);
                    leanh::lean_dec(v_declName_6157_);
                    v_a_6182_ = leanh::lean_ctor_get(v___x_6164_, 0);
                    v_isSharedCheck_6189_ = (!leanh::lean_is_exclusive(v___x_6164_)) as u8;
                    if v_isSharedCheck_6189_ == 0 {
                        v___x_6184_ = v___x_6164_;
                        v_isShared_6185_ = v_isSharedCheck_6189_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6182_);
                        leanh::lean_dec(v___x_6164_);
                        v___x_6184_ = leanh::lean_box(0);
                        v_isShared_6185_ = v_isSharedCheck_6189_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6177_ == 0 {
                    v___x_6179_ = v___x_6176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_a_6174_);
                    v___x_6179_ = v_reuseFailAlloc_6180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6179_;
            }
            3 => {
                if v_isShared_6185_ == 0 {
                    v___x_6187_ = v___x_6184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
                    v___x_6187_ = v_reuseFailAlloc_6188_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst___boxed(
    mut v_declName_6190_: *mut leanh::LeanObject,
    mut v_prio_6191_: *mut leanh::LeanObject,
    mut v_a_6192_: *mut leanh::LeanObject,
    mut v_a_6193_: *mut leanh::LeanObject,
    mut v_a_6194_: *mut leanh::LeanObject,
    mut v_a_6195_: *mut leanh::LeanObject,
    mut v_a_6196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6197_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(
        v_declName_6190_,
        v_prio_6191_,
        v_a_6192_,
        v_a_6193_,
        v_a_6194_,
        v_a_6195_,
    );
    leanh::lean_dec(v_a_6195_);
    leanh::lean_dec_ref(v_a_6194_);
    leanh::lean_dec(v_a_6193_);
    leanh::lean_dec_ref(v_a_6192_);
    return v_res_6197_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6199_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0;
    v___x_6200_ = l_Lean_stringToMessageData(v___x_6199_);
    return v___x_6200_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6202_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2;
    v___x_6203_ = l_Lean_stringToMessageData(v___x_6202_);
    return v___x_6203_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(
    mut v_fvar_6204_: *mut leanh::LeanObject,
    mut v_prio_6205_: *mut leanh::LeanObject,
    mut v_a_6206_: *mut leanh::LeanObject,
    mut v_a_6207_: *mut leanh::LeanObject,
    mut v_a_6208_: *mut leanh::LeanObject,
    mut v_a_6209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6216_: u8 = 0;
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6222_: u8 = 0;
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6232_: u8 = 0;
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvar_6204_);
                v___x_6211_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_6204_, v_a_6206_);
                if leanh::lean_obj_tag(v___x_6211_) == 0 {
                    v_a_6212_ = leanh::lean_ctor_get(v___x_6211_, 0);
                    leanh::lean_inc(v_a_6212_);
                    leanh::lean_dec_ref_known(v___x_6211_, 1);
                    if leanh::lean_obj_tag(v_a_6212_) == 1 {
                        v_val_6213_ = leanh::lean_ctor_get(v_a_6212_, 0);
                        v_isSharedCheck_6222_ = (!leanh::lean_is_exclusive(v_a_6212_)) as u8;
                        if v_isSharedCheck_6222_ == 0 {
                            v___x_6215_ = v_a_6212_;
                            v_isShared_6216_ = v_isSharedCheck_6222_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_6213_);
                            leanh::lean_dec(v_a_6212_);
                            v___x_6215_ = leanh::lean_box(0);
                            v_isShared_6216_ = v_isSharedCheck_6222_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6212_);
                        leanh::lean_dec(v_prio_6205_);
                        v___x_6223_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
                        v___x_6224_ = l_Lean_MessageData_ofName(v_fvar_6204_);
                        v___x_6225_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6225_, 0, v___x_6223_);
                        leanh::lean_ctor_set(v___x_6225_, 1, v___x_6224_);
                        v___x_6226_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
                        v___x_6227_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6227_, 0, v___x_6225_);
                        leanh::lean_ctor_set(v___x_6227_, 1, v___x_6226_);
                        v___x_6228_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_6227_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_);
                        return v___x_6228_;
                    }
                } else {
                    leanh::lean_dec(v_prio_6205_);
                    leanh::lean_dec(v_fvar_6204_);
                    v_a_6229_ = leanh::lean_ctor_get(v___x_6211_, 0);
                    v_isSharedCheck_6236_ = (!leanh::lean_is_exclusive(v___x_6211_)) as u8;
                    if v_isSharedCheck_6236_ == 0 {
                        v___x_6231_ = v___x_6211_;
                        v_isShared_6232_ = v_isSharedCheck_6236_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6229_);
                        leanh::lean_dec(v___x_6211_);
                        v___x_6231_ = leanh::lean_box(0);
                        v_isShared_6232_ = v_isSharedCheck_6236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6217_ = l_Lean_LocalDecl_type(v_val_6213_);
                leanh::lean_dec(v_val_6213_);
                if v_isShared_6216_ == 0 {
                    leanh::lean_ctor_set(v___x_6215_, 0, v_fvar_6204_);
                    v___x_6219_ = v___x_6215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 0, v_fvar_6204_);
                    v___x_6219_ = v_reuseFailAlloc_6221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6220_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v___x_6217_, v___x_6219_, v_prio_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_);
                return v___x_6220_;
            }
            3 => {
                if v_isShared_6232_ == 0 {
                    v___x_6234_ = v___x_6231_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6235_, 0, v_a_6229_);
                    v___x_6234_ = v_reuseFailAlloc_6235_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___boxed(
    mut v_fvar_6237_: *mut leanh::LeanObject,
    mut v_prio_6238_: *mut leanh::LeanObject,
    mut v_a_6239_: *mut leanh::LeanObject,
    mut v_a_6240_: *mut leanh::LeanObject,
    mut v_a_6241_: *mut leanh::LeanObject,
    mut v_a_6242_: *mut leanh::LeanObject,
    mut v_a_6243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6244_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(
        v_fvar_6237_,
        v_prio_6238_,
        v_a_6239_,
        v_a_6240_,
        v_a_6241_,
        v_a_6242_,
    );
    leanh::lean_dec(v_a_6242_);
    leanh::lean_dec_ref(v_a_6241_);
    leanh::lean_dec(v_a_6240_);
    leanh::lean_dec_ref(v_a_6239_);
    return v_res_6244_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(
    mut v___y_6245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6253_: u8 = 0;
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v_r_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut v_unused_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6247_ = lean_st_ref_get(v___y_6245_);
                v_ngen_6248_ = leanh::lean_ctor_get(v___x_6247_, 2);
                leanh::lean_inc_ref(v_ngen_6248_);
                leanh::lean_dec(v___x_6247_);
                v_namePrefix_6249_ = leanh::lean_ctor_get(v_ngen_6248_, 0);
                v_idx_6250_ = leanh::lean_ctor_get(v_ngen_6248_, 1);
                v_isSharedCheck_6279_ = (!leanh::lean_is_exclusive(v_ngen_6248_)) as u8;
                if v_isSharedCheck_6279_ == 0 {
                    v___x_6252_ = v_ngen_6248_;
                    v_isShared_6253_ = v_isSharedCheck_6279_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_6250_);
                    leanh::lean_inc(v_namePrefix_6249_);
                    leanh::lean_dec(v_ngen_6248_);
                    v___x_6252_ = leanh::lean_box(0);
                    v_isShared_6253_ = v_isSharedCheck_6279_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6254_ = lean_st_ref_take(v___y_6245_);
                v_env_6255_ = leanh::lean_ctor_get(v___x_6254_, 0);
                v_nextMacroScope_6256_ = leanh::lean_ctor_get(v___x_6254_, 1);
                v_auxDeclNGen_6257_ = leanh::lean_ctor_get(v___x_6254_, 3);
                v_traceState_6258_ = leanh::lean_ctor_get(v___x_6254_, 4);
                v_cache_6259_ = leanh::lean_ctor_get(v___x_6254_, 5);
                v_messages_6260_ = leanh::lean_ctor_get(v___x_6254_, 6);
                v_infoState_6261_ = leanh::lean_ctor_get(v___x_6254_, 7);
                v_snapshotTasks_6262_ = leanh::lean_ctor_get(v___x_6254_, 8);
                v_isSharedCheck_6277_ = (!leanh::lean_is_exclusive(v___x_6254_)) as u8;
                if v_isSharedCheck_6277_ == 0 {
                    v_unused_6278_ = leanh::lean_ctor_get(v___x_6254_, 2);
                    leanh::lean_dec(v_unused_6278_);
                    v___x_6264_ = v___x_6254_;
                    v_isShared_6265_ = v_isSharedCheck_6277_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6262_);
                    leanh::lean_inc(v_infoState_6261_);
                    leanh::lean_inc(v_messages_6260_);
                    leanh::lean_inc(v_cache_6259_);
                    leanh::lean_inc(v_traceState_6258_);
                    leanh::lean_inc(v_auxDeclNGen_6257_);
                    leanh::lean_inc(v_nextMacroScope_6256_);
                    leanh::lean_inc(v_env_6255_);
                    leanh::lean_dec(v___x_6254_);
                    v___x_6264_ = leanh::lean_box(0);
                    v_isShared_6265_ = v_isSharedCheck_6277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_6250_);
                leanh::lean_inc(v_namePrefix_6249_);
                v_r_6266_ = l_Lean_Name_num___override(v_namePrefix_6249_, v_idx_6250_);
                v___x_6267_ = leanh::lean_unsigned_to_nat(1);
                v___x_6268_ = lean_nat_add(v_idx_6250_, v___x_6267_);
                leanh::lean_dec(v_idx_6250_);
                if v_isShared_6253_ == 0 {
                    leanh::lean_ctor_set(v___x_6252_, 1, v___x_6268_);
                    v___x_6270_ = v___x_6252_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_namePrefix_6249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 1, v___x_6268_);
                    v___x_6270_ = v_reuseFailAlloc_6276_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6265_ == 0 {
                    leanh::lean_ctor_set(v___x_6264_, 2, v___x_6270_);
                    v___x_6272_ = v___x_6264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6275_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_env_6255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 1, v_nextMacroScope_6256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 2, v___x_6270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 3, v_auxDeclNGen_6257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 4, v_traceState_6258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 5, v_cache_6259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 6, v_messages_6260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 7, v_infoState_6261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 8, v_snapshotTasks_6262_);
                    v___x_6272_ = v_reuseFailAlloc_6275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6273_ = lean_st_ref_set(v___y_6245_, v___x_6272_);
                v___x_6274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6274_, 0, v_r_6266_);
                return v___x_6274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(
    mut v___y_6280_: *mut leanh::LeanObject,
    mut v___y_6281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6282_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_6280_);
    leanh::lean_dec(v___y_6280_);
    return v_res_6282_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(
    mut v___y_6283_: *mut leanh::LeanObject,
    mut v___y_6284_: *mut leanh::LeanObject,
    mut v___y_6285_: *mut leanh::LeanObject,
    mut v___y_6286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_6286_);
    return v___x_6288_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(
    mut v___y_6289_: *mut leanh::LeanObject,
    mut v___y_6290_: *mut leanh::LeanObject,
    mut v___y_6291_: *mut leanh::LeanObject,
    mut v___y_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6294_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(
            v___y_6289_,
            v___y_6290_,
            v___y_6291_,
            v___y_6292_,
        );
    leanh::lean_dec(v___y_6292_);
    leanh::lean_dec_ref(v___y_6291_);
    leanh::lean_dec(v___y_6290_);
    leanh::lean_dec_ref(v___y_6289_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(
    mut v_ref_6295_: *mut leanh::LeanObject,
    mut v_proof_6296_: *mut leanh::LeanObject,
    mut v_prio_6297_: *mut leanh::LeanObject,
    mut v_a_6298_: *mut leanh::LeanObject,
    mut v_a_6299_: *mut leanh::LeanObject,
    mut v_a_6300_: *mut leanh::LeanObject,
    mut v_a_6301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6312_: u8 = 0;
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_6301_);
                leanh::lean_inc_ref(v_a_6300_);
                leanh::lean_inc(v_a_6299_);
                leanh::lean_inc_ref(v_a_6298_);
                leanh::lean_inc_ref(v_proof_6296_);
                v___x_6303_ =
                    lean_infer_type(v_proof_6296_, v_a_6298_, v_a_6299_, v_a_6300_, v_a_6301_);
                if leanh::lean_obj_tag(v___x_6303_) == 0 {
                    v_a_6304_ = leanh::lean_ctor_get(v___x_6303_, 0);
                    leanh::lean_inc(v_a_6304_);
                    leanh::lean_dec_ref_known(v___x_6303_, 1);
                    v___x_6305_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_6301_);
                    v_a_6306_ = leanh::lean_ctor_get(v___x_6305_, 0);
                    leanh::lean_inc(v_a_6306_);
                    leanh::lean_dec_ref(v___x_6305_);
                    v___x_6307_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_6307_, 0, v_a_6306_);
                    leanh::lean_ctor_set(v___x_6307_, 1, v_ref_6295_);
                    leanh::lean_ctor_set(v___x_6307_, 2, v_proof_6296_);
                    v___x_6308_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_6304_, v___x_6307_, v_prio_6297_, v_a_6298_, v_a_6299_, v_a_6300_, v_a_6301_);
                    return v___x_6308_;
                } else {
                    leanh::lean_dec(v_prio_6297_);
                    leanh::lean_dec_ref(v_proof_6296_);
                    leanh::lean_dec(v_ref_6295_);
                    v_a_6309_ = leanh::lean_ctor_get(v___x_6303_, 0);
                    v_isSharedCheck_6316_ = (!leanh::lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6316_ == 0 {
                        v___x_6311_ = v___x_6303_;
                        v_isShared_6312_ = v_isSharedCheck_6316_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6309_);
                        leanh::lean_dec(v___x_6303_);
                        v___x_6311_ = leanh::lean_box(0);
                        v_isShared_6312_ = v_isSharedCheck_6316_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6312_ == 0 {
                    v___x_6314_ = v___x_6311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6315_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6315_, 0, v_a_6309_);
                    v___x_6314_ = v_reuseFailAlloc_6315_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx___boxed(
    mut v_ref_6317_: *mut leanh::LeanObject,
    mut v_proof_6318_: *mut leanh::LeanObject,
    mut v_prio_6319_: *mut leanh::LeanObject,
    mut v_a_6320_: *mut leanh::LeanObject,
    mut v_a_6321_: *mut leanh::LeanObject,
    mut v_a_6322_: *mut leanh::LeanObject,
    mut v_a_6323_: *mut leanh::LeanObject,
    mut v_a_6324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(
        v_ref_6317_,
        v_proof_6318_,
        v_prio_6319_,
        v_a_6320_,
        v_a_6321_,
        v_a_6322_,
        v_a_6323_,
    );
    leanh::lean_dec(v_a_6323_);
    leanh::lean_dec_ref(v_a_6322_);
    leanh::lean_dec(v_a_6321_);
    leanh::lean_dec_ref(v_a_6320_);
    return v_res_6325_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6326_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6326_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6327_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
    v___x_6328_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6328_, 0, v___x_6327_);
    return v___x_6328_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6329_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
    v___x_6330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6330_, 0, v___x_6329_);
    leanh::lean_ctor_set(v___x_6330_, 1, v___x_6329_);
    return v___x_6330_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6331_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
    v___x_6332_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_6332_, 0, v___x_6331_);
    leanh::lean_ctor_set(v___x_6332_, 1, v___x_6331_);
    leanh::lean_ctor_set(v___x_6332_, 2, v___x_6331_);
    leanh::lean_ctor_set(v___x_6332_, 3, v___x_6331_);
    leanh::lean_ctor_set(v___x_6332_, 4, v___x_6331_);
    leanh::lean_ctor_set(v___x_6332_, 5, v___x_6331_);
    return v___x_6332_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(
    mut v_ext_6333_: *mut leanh::LeanObject,
    mut v_b_6334_: *mut leanh::LeanObject,
    mut v_kind_6335_: u8,
    mut v___y_6336_: *mut leanh::LeanObject,
    mut v___y_6337_: *mut leanh::LeanObject,
    mut v___y_6338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_currNamespace_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6352_: u8 = 0;
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_unused_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6376_: u8 = 0;
    let mut v_unused_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_6340_ = leanh::lean_ctor_get(v___y_6337_, 6);
                v___x_6341_ = lean_st_ref_take(v___y_6338_);
                v_env_6342_ = leanh::lean_ctor_get(v___x_6341_, 0);
                v_nextMacroScope_6343_ = leanh::lean_ctor_get(v___x_6341_, 1);
                v_ngen_6344_ = leanh::lean_ctor_get(v___x_6341_, 2);
                v_auxDeclNGen_6345_ = leanh::lean_ctor_get(v___x_6341_, 3);
                v_traceState_6346_ = leanh::lean_ctor_get(v___x_6341_, 4);
                v_messages_6347_ = leanh::lean_ctor_get(v___x_6341_, 6);
                v_infoState_6348_ = leanh::lean_ctor_get(v___x_6341_, 7);
                v_snapshotTasks_6349_ = leanh::lean_ctor_get(v___x_6341_, 8);
                v_isSharedCheck_6376_ = (!leanh::lean_is_exclusive(v___x_6341_)) as u8;
                if v_isSharedCheck_6376_ == 0 {
                    v_unused_6377_ = leanh::lean_ctor_get(v___x_6341_, 5);
                    leanh::lean_dec(v_unused_6377_);
                    v___x_6351_ = v___x_6341_;
                    v_isShared_6352_ = v_isSharedCheck_6376_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6349_);
                    leanh::lean_inc(v_infoState_6348_);
                    leanh::lean_inc(v_messages_6347_);
                    leanh::lean_inc(v_traceState_6346_);
                    leanh::lean_inc(v_auxDeclNGen_6345_);
                    leanh::lean_inc(v_ngen_6344_);
                    leanh::lean_inc(v_nextMacroScope_6343_);
                    leanh::lean_inc(v_env_6342_);
                    leanh::lean_dec(v___x_6341_);
                    v___x_6351_ = leanh::lean_box(0);
                    v_isShared_6352_ = v_isSharedCheck_6376_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_currNamespace_6340_);
                v___x_6353_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_6342_,
                    v_ext_6333_,
                    v_b_6334_,
                    v_kind_6335_,
                    v_currNamespace_6340_,
                );
                v___x_6354_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
                if v_isShared_6352_ == 0 {
                    leanh::lean_ctor_set(v___x_6351_, 5, v___x_6354_);
                    leanh::lean_ctor_set(v___x_6351_, 0, v___x_6353_);
                    v___x_6356_ = v___x_6351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6375_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 0, v___x_6353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 1, v_nextMacroScope_6343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 2, v_ngen_6344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 3, v_auxDeclNGen_6345_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 4, v_traceState_6346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 5, v___x_6354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 6, v_messages_6347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 7, v_infoState_6348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 8, v_snapshotTasks_6349_);
                    v___x_6356_ = v_reuseFailAlloc_6375_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6357_ = lean_st_ref_set(v___y_6338_, v___x_6356_);
                v___x_6358_ = lean_st_ref_take(v___y_6336_);
                v_mctx_6359_ = leanh::lean_ctor_get(v___x_6358_, 0);
                v_zetaDeltaFVarIds_6360_ = leanh::lean_ctor_get(v___x_6358_, 2);
                v_postponed_6361_ = leanh::lean_ctor_get(v___x_6358_, 3);
                v_diag_6362_ = leanh::lean_ctor_get(v___x_6358_, 4);
                v_isSharedCheck_6373_ = (!leanh::lean_is_exclusive(v___x_6358_)) as u8;
                if v_isSharedCheck_6373_ == 0 {
                    v_unused_6374_ = leanh::lean_ctor_get(v___x_6358_, 1);
                    leanh::lean_dec(v_unused_6374_);
                    v___x_6364_ = v___x_6358_;
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6362_);
                    leanh::lean_inc(v_postponed_6361_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6360_);
                    leanh::lean_inc(v_mctx_6359_);
                    leanh::lean_dec(v___x_6358_);
                    v___x_6364_ = leanh::lean_box(0);
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6366_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
                if v_isShared_6365_ == 0 {
                    leanh::lean_ctor_set(v___x_6364_, 1, v___x_6366_);
                    v___x_6368_ = v___x_6364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6372_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_mctx_6359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 1, v___x_6366_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6372_,
                        2,
                        v_zetaDeltaFVarIds_6360_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 3, v_postponed_6361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 4, v_diag_6362_);
                    v___x_6368_ = v_reuseFailAlloc_6372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6369_ = lean_st_ref_set(v___y_6336_, v___x_6368_);
                v___x_6370_ = leanh::lean_box(0);
                v___x_6371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6371_, 0, v___x_6370_);
                return v___x_6371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(
    mut v_ext_6378_: *mut leanh::LeanObject,
    mut v_b_6379_: *mut leanh::LeanObject,
    mut v_kind_6380_: *mut leanh::LeanObject,
    mut v___y_6381_: *mut leanh::LeanObject,
    mut v___y_6382_: *mut leanh::LeanObject,
    mut v___y_6383_: *mut leanh::LeanObject,
    mut v___y_6384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6385_: u8 = 0;
    let mut v_res_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6385_ = (leanh::lean_unbox(v_kind_6380_) as u8);
    v_res_6386_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6378_, v_b_6379_, v_kind_boxed_6385_, v___y_6381_, v___y_6382_, v___y_6383_);
    leanh::lean_dec(v___y_6383_);
    leanh::lean_dec_ref(v___y_6382_);
    leanh::lean_dec(v___y_6381_);
    return v_res_6386_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(
    mut v_00_u03b1_6387_: *mut leanh::LeanObject,
    mut v_00_u03b2_6388_: *mut leanh::LeanObject,
    mut v_00_u03c3_6389_: *mut leanh::LeanObject,
    mut v_ext_6390_: *mut leanh::LeanObject,
    mut v_b_6391_: *mut leanh::LeanObject,
    mut v_kind_6392_: u8,
    mut v___y_6393_: *mut leanh::LeanObject,
    mut v___y_6394_: *mut leanh::LeanObject,
    mut v___y_6395_: *mut leanh::LeanObject,
    mut v___y_6396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6398_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6390_, v_b_6391_, v_kind_6392_, v___y_6394_, v___y_6395_, v___y_6396_);
    return v___x_6398_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(
    mut v_00_u03b1_6399_: *mut leanh::LeanObject,
    mut v_00_u03b2_6400_: *mut leanh::LeanObject,
    mut v_00_u03c3_6401_: *mut leanh::LeanObject,
    mut v_ext_6402_: *mut leanh::LeanObject,
    mut v_b_6403_: *mut leanh::LeanObject,
    mut v_kind_6404_: *mut leanh::LeanObject,
    mut v___y_6405_: *mut leanh::LeanObject,
    mut v___y_6406_: *mut leanh::LeanObject,
    mut v___y_6407_: *mut leanh::LeanObject,
    mut v___y_6408_: *mut leanh::LeanObject,
    mut v___y_6409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6410_: u8 = 0;
    let mut v_res_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6410_ = (leanh::lean_unbox(v_kind_6404_) as u8);
    v_res_6411_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_6399_, v_00_u03b2_6400_, v_00_u03c3_6401_, v_ext_6402_, v_b_6403_, v_kind_boxed_6410_, v___y_6405_, v___y_6406_, v___y_6407_, v___y_6408_);
    leanh::lean_dec(v___y_6408_);
    leanh::lean_dec_ref(v___y_6407_);
    leanh::lean_dec(v___y_6406_);
    leanh::lean_dec_ref(v___y_6405_);
    return v_res_6411_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(
    mut v_ext_6412_: *mut leanh::LeanObject,
    mut v_declName_6413_: *mut leanh::LeanObject,
    mut v_prio_6414_: *mut leanh::LeanObject,
    mut v_attrKind_6415_: u8,
    mut v_a_6416_: *mut leanh::LeanObject,
    mut v_a_6417_: *mut leanh::LeanObject,
    mut v_a_6418_: *mut leanh::LeanObject,
    mut v_a_6419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6427_: u8 = 0;
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6421_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(
                    v_declName_6413_,
                    v_prio_6414_,
                    v_a_6416_,
                    v_a_6417_,
                    v_a_6418_,
                    v_a_6419_,
                );
                if leanh::lean_obj_tag(v___x_6421_) == 0 {
                    v_a_6422_ = leanh::lean_ctor_get(v___x_6421_, 0);
                    leanh::lean_inc(v_a_6422_);
                    leanh::lean_dec_ref_known(v___x_6421_, 1);
                    v___x_6423_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6412_, v_a_6422_, v_attrKind_6415_, v_a_6417_, v_a_6418_, v_a_6419_);
                    return v___x_6423_;
                } else {
                    leanh::lean_dec_ref(v_ext_6412_);
                    v_a_6424_ = leanh::lean_ctor_get(v___x_6421_, 0);
                    v_isSharedCheck_6431_ = (!leanh::lean_is_exclusive(v___x_6421_)) as u8;
                    if v_isSharedCheck_6431_ == 0 {
                        v___x_6426_ = v___x_6421_;
                        v_isShared_6427_ = v_isSharedCheck_6431_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6424_);
                        leanh::lean_dec(v___x_6421_);
                        v___x_6426_ = leanh::lean_box(0);
                        v_isShared_6427_ = v_isSharedCheck_6431_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6427_ == 0 {
                    v___x_6429_ = v___x_6426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6424_);
                    v___x_6429_ = v_reuseFailAlloc_6430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst___boxed(
    mut v_ext_6432_: *mut leanh::LeanObject,
    mut v_declName_6433_: *mut leanh::LeanObject,
    mut v_prio_6434_: *mut leanh::LeanObject,
    mut v_attrKind_6435_: *mut leanh::LeanObject,
    mut v_a_6436_: *mut leanh::LeanObject,
    mut v_a_6437_: *mut leanh::LeanObject,
    mut v_a_6438_: *mut leanh::LeanObject,
    mut v_a_6439_: *mut leanh::LeanObject,
    mut v_a_6440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_attrKind_boxed_6441_: u8 = 0;
    let mut v_res_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6441_ = (leanh::lean_unbox(v_attrKind_6435_) as u8);
    v_res_6442_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(
        v_ext_6432_,
        v_declName_6433_,
        v_prio_6434_,
        v_attrKind_boxed_6441_,
        v_a_6436_,
        v_a_6437_,
        v_a_6438_,
        v_a_6439_,
    );
    leanh::lean_dec(v_a_6439_);
    leanh::lean_dec_ref(v_a_6438_);
    leanh::lean_dec(v_a_6437_);
    leanh::lean_dec_ref(v_a_6436_);
    return v_res_6442_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(
    mut v_ext_6443_: *mut leanh::LeanObject,
    mut v_fvar_6444_: *mut leanh::LeanObject,
    mut v_prio_6445_: *mut leanh::LeanObject,
    mut v_a_6446_: *mut leanh::LeanObject,
    mut v_a_6447_: *mut leanh::LeanObject,
    mut v_a_6448_: *mut leanh::LeanObject,
    mut v_a_6449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: u8 = 0;
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6458_: u8 = 0;
    let mut v___x_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6451_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(
                    v_fvar_6444_,
                    v_prio_6445_,
                    v_a_6446_,
                    v_a_6447_,
                    v_a_6448_,
                    v_a_6449_,
                );
                if leanh::lean_obj_tag(v___x_6451_) == 0 {
                    v_a_6452_ = leanh::lean_ctor_get(v___x_6451_, 0);
                    leanh::lean_inc(v_a_6452_);
                    leanh::lean_dec_ref_known(v___x_6451_, 1);
                    v___x_6453_ = 1;
                    v___x_6454_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6443_, v_a_6452_, v___x_6453_, v_a_6447_, v_a_6448_, v_a_6449_);
                    return v___x_6454_;
                } else {
                    leanh::lean_dec_ref(v_ext_6443_);
                    v_a_6455_ = leanh::lean_ctor_get(v___x_6451_, 0);
                    v_isSharedCheck_6462_ = (!leanh::lean_is_exclusive(v___x_6451_)) as u8;
                    if v_isSharedCheck_6462_ == 0 {
                        v___x_6457_ = v___x_6451_;
                        v_isShared_6458_ = v_isSharedCheck_6462_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6455_);
                        leanh::lean_dec(v___x_6451_);
                        v___x_6457_ = leanh::lean_box(0);
                        v_isShared_6458_ = v_isSharedCheck_6462_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6458_ == 0 {
                    v___x_6460_ = v___x_6457_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
                    v___x_6460_ = v_reuseFailAlloc_6461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal___boxed(
    mut v_ext_6463_: *mut leanh::LeanObject,
    mut v_fvar_6464_: *mut leanh::LeanObject,
    mut v_prio_6465_: *mut leanh::LeanObject,
    mut v_a_6466_: *mut leanh::LeanObject,
    mut v_a_6467_: *mut leanh::LeanObject,
    mut v_a_6468_: *mut leanh::LeanObject,
    mut v_a_6469_: *mut leanh::LeanObject,
    mut v_a_6470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6471_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(
        v_ext_6463_,
        v_fvar_6464_,
        v_prio_6465_,
        v_a_6466_,
        v_a_6467_,
        v_a_6468_,
        v_a_6469_,
    );
    leanh::lean_dec(v_a_6469_);
    leanh::lean_dec_ref(v_a_6468_);
    leanh::lean_dec(v_a_6467_);
    leanh::lean_dec_ref(v_a_6466_);
    return v_res_6471_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(
    mut v_x_6472_: *mut leanh::LeanObject,
    mut v_a_6473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6474_, 0, v_a_6473_);
    leanh::lean_inc_ref_n(v___x_6474_, 2);
    v___x_6475_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6475_, 0, v___x_6474_);
    leanh::lean_ctor_set(v___x_6475_, 1, v___x_6474_);
    leanh::lean_ctor_set(v___x_6475_, 2, v___x_6474_);
    return v___x_6475_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(
    mut v_x_6476_: *mut leanh::LeanObject,
    mut v_a_6477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6478_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_6476_, v_a_6477_);
    leanh::lean_dec_ref(v_x_6476_);
    return v_res_6478_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(
    mut v___y_6479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_6479_);
    return v___y_6479_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(
    mut v___y_6480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6481_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_6480_);
    leanh::lean_dec_ref(v___y_6480_);
    return v_res_6481_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5()
-> *mut leanh::LeanObject {
    let mut v___f_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6488_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1;
    v___f_6489_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2;
    v___x_6490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2,
    );
    v___f_6491_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0;
    v___x_6492_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4;
    v___x_6493_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_6493_, 0, v___x_6492_);
    leanh::lean_ctor_set(v___x_6493_, 1, v___f_6491_);
    leanh::lean_ctor_set(v___x_6493_, 2, v___x_6490_);
    leanh::lean_ctor_set(v___x_6493_, 3, v___f_6489_);
    leanh::lean_ctor_set(v___x_6493_, 4, v___f_6488_);
    return v___x_6493_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt() -> *mut leanh::LeanObject {
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5,
    );
    return v___x_6494_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6496_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
    v___x_6497_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_6496_);
    return v___x_6497_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(
    mut v_a_6498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6499_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
    return v_res_6499_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6501_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0;
    v___x_6502_ = l_Lean_stringToMessageData(v___x_6501_);
    return v___x_6502_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(
    mut v_____r_6503_: *mut leanh::LeanObject,
    mut v___y_6504_: *mut leanh::LeanObject,
    mut v___y_6505_: *mut leanh::LeanObject,
    mut v___y_6506_: *mut leanh::LeanObject,
    mut v___y_6507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6509_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1,
    );
    v___x_6510_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_6509_, v___y_6504_, v___y_6505_, v___y_6506_, v___y_6507_);
    return v___x_6510_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed(
    mut v_____r_6511_: *mut leanh::LeanObject,
    mut v___y_6512_: *mut leanh::LeanObject,
    mut v___y_6513_: *mut leanh::LeanObject,
    mut v___y_6514_: *mut leanh::LeanObject,
    mut v___y_6515_: *mut leanh::LeanObject,
    mut v___y_6516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6517_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(
        v_____r_6511_,
        v___y_6512_,
        v___y_6513_,
        v___y_6514_,
        v___y_6515_,
    );
    leanh::lean_dec(v___y_6515_);
    leanh::lean_dec_ref(v___y_6514_);
    leanh::lean_dec(v___y_6513_);
    leanh::lean_dec_ref(v___y_6512_);
    return v_res_6517_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0()
-> f64 {
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: f64 = 0.0;
    v___x_6518_ = leanh::lean_unsigned_to_nat(0);
    v___x_6519_ = lean_float_of_nat(v___x_6518_);
    return v___x_6519_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(
    mut v_cls_6523_: *mut leanh::LeanObject,
    mut v_msg_6524_: *mut leanh::LeanObject,
    mut v___y_6525_: *mut leanh::LeanObject,
    mut v___y_6526_: *mut leanh::LeanObject,
    mut v___y_6527_: *mut leanh::LeanObject,
    mut v___y_6528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6535_: u8 = 0;
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6548_: u8 = 0;
    let mut v_tid_6549_: u64 = 0;
    let mut v_traces_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6553_: u8 = 0;
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: f64 = 0.0;
    let mut v___x_6556_: u8 = 0;
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6574_: u8 = 0;
    let mut v_isSharedCheck_6575_: u8 = 0;
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6530_ = leanh::lean_ctor_get(v___y_6527_, 5);
                v___x_6531_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
                v_a_6532_ = leanh::lean_ctor_get(v___x_6531_, 0);
                v_isSharedCheck_6576_ = (!leanh::lean_is_exclusive(v___x_6531_)) as u8;
                if v_isSharedCheck_6576_ == 0 {
                    v___x_6534_ = v___x_6531_;
                    v_isShared_6535_ = v_isSharedCheck_6576_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6532_);
                    leanh::lean_dec(v___x_6531_);
                    v___x_6534_ = leanh::lean_box(0);
                    v_isShared_6535_ = v_isSharedCheck_6576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6536_ = lean_st_ref_take(v___y_6528_);
                v_traceState_6537_ = leanh::lean_ctor_get(v___x_6536_, 4);
                v_env_6538_ = leanh::lean_ctor_get(v___x_6536_, 0);
                v_nextMacroScope_6539_ = leanh::lean_ctor_get(v___x_6536_, 1);
                v_ngen_6540_ = leanh::lean_ctor_get(v___x_6536_, 2);
                v_auxDeclNGen_6541_ = leanh::lean_ctor_get(v___x_6536_, 3);
                v_cache_6542_ = leanh::lean_ctor_get(v___x_6536_, 5);
                v_messages_6543_ = leanh::lean_ctor_get(v___x_6536_, 6);
                v_infoState_6544_ = leanh::lean_ctor_get(v___x_6536_, 7);
                v_snapshotTasks_6545_ = leanh::lean_ctor_get(v___x_6536_, 8);
                v_isSharedCheck_6575_ = (!leanh::lean_is_exclusive(v___x_6536_)) as u8;
                if v_isSharedCheck_6575_ == 0 {
                    v___x_6547_ = v___x_6536_;
                    v_isShared_6548_ = v_isSharedCheck_6575_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6545_);
                    leanh::lean_inc(v_infoState_6544_);
                    leanh::lean_inc(v_messages_6543_);
                    leanh::lean_inc(v_cache_6542_);
                    leanh::lean_inc(v_traceState_6537_);
                    leanh::lean_inc(v_auxDeclNGen_6541_);
                    leanh::lean_inc(v_ngen_6540_);
                    leanh::lean_inc(v_nextMacroScope_6539_);
                    leanh::lean_inc(v_env_6538_);
                    leanh::lean_dec(v___x_6536_);
                    v___x_6547_ = leanh::lean_box(0);
                    v_isShared_6548_ = v_isSharedCheck_6575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6549_ = leanh::lean_ctor_get_uint64(
                    v_traceState_6537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6550_ = leanh::lean_ctor_get(v_traceState_6537_, 0);
                v_isSharedCheck_6574_ =
                    (!leanh::lean_is_exclusive(v_traceState_6537_)) as u8;
                if v_isSharedCheck_6574_ == 0 {
                    v___x_6552_ = v_traceState_6537_;
                    v_isShared_6553_ = v_isSharedCheck_6574_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_6550_);
                    leanh::lean_dec(v_traceState_6537_);
                    v___x_6552_ = leanh::lean_box(0);
                    v_isShared_6553_ = v_isSharedCheck_6574_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6554_ = leanh::lean_box(0);
                v___x_6555_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0);
                v___x_6556_ = 0;
                v___x_6557_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1;
                v___x_6558_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_6558_, 0, v_cls_6523_);
                leanh::lean_ctor_set(v___x_6558_, 1, v___x_6554_);
                leanh::lean_ctor_set(v___x_6558_, 2, v___x_6557_);
                leanh::lean_ctor_set_float(
                    v___x_6558_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_6555_,
                );
                leanh::lean_ctor_set_float(
                    v___x_6558_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6555_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6558_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6556_,
                );
                v___x_6559_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2;
                v___x_6560_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6560_, 0, v___x_6558_);
                leanh::lean_ctor_set(v___x_6560_, 1, v_a_6532_);
                leanh::lean_ctor_set(v___x_6560_, 2, v___x_6559_);
                leanh::lean_inc(v_ref_6530_);
                v___x_6561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6561_, 0, v_ref_6530_);
                leanh::lean_ctor_set(v___x_6561_, 1, v___x_6560_);
                v___x_6562_ = l_Lean_PersistentArray_push___redArg(v_traces_6550_, v___x_6561_);
                if v_isShared_6553_ == 0 {
                    leanh::lean_ctor_set(v___x_6552_, 0, v___x_6562_);
                    v___x_6564_ = v___x_6552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6573_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6573_, 0, v___x_6562_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6573_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_6549_,
                    );
                    v___x_6564_ = v_reuseFailAlloc_6573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6548_ == 0 {
                    leanh::lean_ctor_set(v___x_6547_, 4, v___x_6564_);
                    v___x_6566_ = v___x_6547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6572_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_env_6538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 1, v_nextMacroScope_6539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 2, v_ngen_6540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 3, v_auxDeclNGen_6541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 4, v___x_6564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 5, v_cache_6542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 6, v_messages_6543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 7, v_infoState_6544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 8, v_snapshotTasks_6545_);
                    v___x_6566_ = v_reuseFailAlloc_6572_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6567_ = lean_st_ref_set(v___y_6528_, v___x_6566_);
                v___x_6568_ = leanh::lean_box(0);
                if v_isShared_6535_ == 0 {
                    leanh::lean_ctor_set(v___x_6534_, 0, v___x_6568_);
                    v___x_6570_ = v___x_6534_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 0, v___x_6568_);
                    v___x_6570_ = v_reuseFailAlloc_6571_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___boxed(
    mut v_cls_6577_: *mut leanh::LeanObject,
    mut v_msg_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
    mut v___y_6580_: *mut leanh::LeanObject,
    mut v___y_6581_: *mut leanh::LeanObject,
    mut v___y_6582_: *mut leanh::LeanObject,
    mut v___y_6583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6584_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(
        v_cls_6577_,
        v_msg_6578_,
        v___y_6579_,
        v___y_6580_,
        v___y_6581_,
        v___y_6582_,
    );
    leanh::lean_dec(v___y_6582_);
    leanh::lean_dec_ref(v___y_6581_);
    leanh::lean_dec(v___y_6580_);
    leanh::lean_dec_ref(v___y_6579_);
    return v_res_6584_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(
    mut v_constName_6585_: *mut leanh::LeanObject,
    mut v_skipRealize_6586_: u8,
    mut v___y_6587_: *mut leanh::LeanObject,
    mut v___y_6588_: *mut leanh::LeanObject,
    mut v___y_6589_: *mut leanh::LeanObject,
    mut v___y_6590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6592_ = lean_st_ref_get(v___y_6590_);
                v_env_6593_ = leanh::lean_ctor_get(v___x_6592_, 0);
                leanh::lean_inc_ref(v_env_6593_);
                leanh::lean_dec(v___x_6592_);
                leanh::lean_inc(v_constName_6585_);
                v___x_6594_ = l_Lean_Environment_findAsync_x3f(
                    v_env_6593_,
                    v_constName_6585_,
                    v_skipRealize_6586_,
                );
                if leanh::lean_obj_tag(v___x_6594_) == 0 {
                    v___x_6595_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_6585_, v___y_6587_, v___y_6588_, v___y_6589_, v___y_6590_);
                    return v___x_6595_;
                } else {
                    leanh::lean_dec(v_constName_6585_);
                    v_val_6596_ = leanh::lean_ctor_get(v___x_6594_, 0);
                    v_isSharedCheck_6603_ = (!leanh::lean_is_exclusive(v___x_6594_)) as u8;
                    if v_isSharedCheck_6603_ == 0 {
                        v___x_6598_ = v___x_6594_;
                        v_isShared_6599_ = v_isSharedCheck_6603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6596_);
                        leanh::lean_dec(v___x_6594_);
                        v___x_6598_ = leanh::lean_box(0);
                        v_isShared_6599_ = v_isSharedCheck_6603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6599_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6598_, 0);
                    v___x_6601_ = v___x_6598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_val_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0___boxed(
    mut v_constName_6604_: *mut leanh::LeanObject,
    mut v_skipRealize_6605_: *mut leanh::LeanObject,
    mut v___y_6606_: *mut leanh::LeanObject,
    mut v___y_6607_: *mut leanh::LeanObject,
    mut v___y_6608_: *mut leanh::LeanObject,
    mut v___y_6609_: *mut leanh::LeanObject,
    mut v___y_6610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_6611_: u8 = 0;
    let mut v_res_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_6611_ = (leanh::lean_unbox(v_skipRealize_6605_) as u8);
    v_res_6612_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(
        v_constName_6604_,
        v_skipRealize_boxed_6611_,
        v___y_6606_,
        v___y_6607_,
        v___y_6608_,
        v___y_6609_,
    );
    leanh::lean_dec(v___y_6609_);
    leanh::lean_dec_ref(v___y_6608_);
    leanh::lean_dec(v___y_6607_);
    leanh::lean_dec_ref(v___y_6606_);
    return v_res_6612_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1() -> u64 {
    let mut v___x_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: u64 = 0;
    v___x_6619_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0;
    v___x_6620_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6619_);
    return v___x_6620_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6621_: u64 = 0;
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6621_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1,
    );
    v___x_6622_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0;
    v___x_6623_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_6623_, 0, v___x_6622_);
    leanh::lean_ctor_set_uint64(
        v___x_6623_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_6621_,
    );
    return v___x_6623_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6624_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6624_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6625_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3,
    );
    v___x_6626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6626_, 0, v___x_6625_);
    return v___x_6626_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6627_ = leanh::lean_box(1);
    v___x_6628_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_6629_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6630_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6630_, 0, v___x_6629_);
    leanh::lean_ctor_set(v___x_6630_, 1, v___x_6628_);
    leanh::lean_ctor_set(v___x_6630_, 2, v___x_6627_);
    return v___x_6630_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6633_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6634_ = leanh::lean_unsigned_to_nat(0);
    v___x_6635_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_6635_, 0, v___x_6634_);
    leanh::lean_ctor_set(v___x_6635_, 1, v___x_6634_);
    leanh::lean_ctor_set(v___x_6635_, 2, v___x_6634_);
    leanh::lean_ctor_set(v___x_6635_, 3, v___x_6634_);
    leanh::lean_ctor_set(v___x_6635_, 4, v___x_6633_);
    leanh::lean_ctor_set(v___x_6635_, 5, v___x_6633_);
    leanh::lean_ctor_set(v___x_6635_, 6, v___x_6633_);
    leanh::lean_ctor_set(v___x_6635_, 7, v___x_6633_);
    leanh::lean_ctor_set(v___x_6635_, 8, v___x_6633_);
    leanh::lean_ctor_set(v___x_6635_, 9, v___x_6633_);
    return v___x_6635_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6636_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6637_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_6637_, 0, v___x_6636_);
    leanh::lean_ctor_set(v___x_6637_, 1, v___x_6636_);
    leanh::lean_ctor_set(v___x_6637_, 2, v___x_6636_);
    leanh::lean_ctor_set(v___x_6637_, 3, v___x_6636_);
    leanh::lean_ctor_set(v___x_6637_, 4, v___x_6636_);
    leanh::lean_ctor_set(v___x_6637_, 5, v___x_6636_);
    return v___x_6637_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6638_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6639_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_6639_, 0, v___x_6638_);
    leanh::lean_ctor_set(v___x_6639_, 1, v___x_6638_);
    leanh::lean_ctor_set(v___x_6639_, 2, v___x_6638_);
    leanh::lean_ctor_set(v___x_6639_, 3, v___x_6638_);
    leanh::lean_ctor_set(v___x_6639_, 4, v___x_6638_);
    return v___x_6639_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6644_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12;
    v___x_6645_ = l_Lean_stringToMessageData(v___x_6644_);
    return v___x_6645_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6646_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_6647_ = l_String_toRawSubstring_x27(v___x_6646_);
    return v___x_6647_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6651_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_6651_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(
    mut v___x_6654_: *mut leanh::LeanObject,
    mut v_ext_6655_: *mut leanh::LeanObject,
    mut v___f_6656_: *mut leanh::LeanObject,
    mut v___x_6657_: *mut leanh::LeanObject,
    mut v___x_6658_: *mut leanh::LeanObject,
    mut v___x_6659_: *mut leanh::LeanObject,
    mut v___x_6660_: *mut leanh::LeanObject,
    mut v_declName_6661_: *mut leanh::LeanObject,
    mut v_stx_6662_: *mut leanh::LeanObject,
    mut v_attrKind_6663_: u8,
    mut v___y_6664_: *mut leanh::LeanObject,
    mut v___y_6665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6667_: u8 = 0;
    let mut v___x_6668_: u8 = 0;
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6688_: u8 = 0;
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6704_: u8 = 0;
    let mut v_hasTrace_6705_: u8 = 0;
    let mut v___x_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: u8 = 0;
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6720_: u8 = 0;
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_add_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6740_: u8 = 0;
    let mut v___x_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: u8 = 0;
    let mut v___x_6756_: u8 = 0;
    let mut v_reuseFailAlloc_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_unused_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v_ref_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6775_: u8 = 0;
    let mut v_isSharedCheck_6776_: u8 = 0;
    let mut v_unused_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: u8 = 0;
    let mut v___x_6779_: u8 = 0;
    let mut v_isSharedCheck_6780_: u8 = 0;
    let mut v_a_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6788_: u8 = 0;
    let mut v_a_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6792_: u8 = 0;
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6667_ = 0;
                v___x_6668_ = 1;
                v___x_6669_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2,
                );
                v___x_6670_ = leanh::lean_unsigned_to_nat(0);
                v___x_6671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
                v___x_6672_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5,
                );
                v___x_6673_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6;
                v___x_6674_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_6654_);
                v___x_6675_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_6675_, 0, v___x_6669_);
                leanh::lean_ctor_set(v___x_6675_, 1, v___x_6654_);
                leanh::lean_ctor_set(v___x_6675_, 2, v___x_6672_);
                leanh::lean_ctor_set(v___x_6675_, 3, v___x_6673_);
                leanh::lean_ctor_set(v___x_6675_, 4, v___x_6674_);
                leanh::lean_ctor_set(v___x_6675_, 5, v___x_6670_);
                leanh::lean_ctor_set(v___x_6675_, 6, v___x_6674_);
                leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___x_6667_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_6667_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_6667_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_6668_,
                );
                v___x_6676_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7,
                );
                v___x_6677_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8,
                );
                v___x_6678_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9,
                );
                v___x_6679_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6679_, 0, v___x_6676_);
                leanh::lean_ctor_set(v___x_6679_, 1, v___x_6677_);
                leanh::lean_ctor_set(v___x_6679_, 2, v___x_6654_);
                leanh::lean_ctor_set(v___x_6679_, 3, v___x_6671_);
                leanh::lean_ctor_set(v___x_6679_, 4, v___x_6678_);
                v___x_6680_ = lean_st_mk_ref(v___x_6679_);
                leanh::lean_inc(v_declName_6661_);
                v___x_6681_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_6661_, v___x_6667_, v___x_6675_, v___x_6680_, v___y_6664_, v___y_6665_);
                if leanh::lean_obj_tag(v___x_6681_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6681_, 1);
                    v___x_6682_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6683_ = l_Lean_Syntax_getArg(v_stx_6662_, v___x_6682_);
                    leanh::lean_inc(v___x_6683_);
                    v___x_6684_ = l_Lean_getAttrParamOptPrio(v___x_6683_, v___y_6664_, v___y_6665_);
                    if leanh::lean_obj_tag(v___x_6684_) == 0 {
                        v_a_6685_ = leanh::lean_ctor_get(v___x_6684_, 0);
                        v_isSharedCheck_6780_ =
                            (!leanh::lean_is_exclusive(v___x_6684_)) as u8;
                        if v_isSharedCheck_6780_ == 0 {
                            v___x_6687_ = v___x_6684_;
                            v_isShared_6688_ = v_isSharedCheck_6780_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6685_);
                            leanh::lean_dec(v___x_6684_);
                            v___x_6687_ = leanh::lean_box(0);
                            v_isShared_6688_ = v_isSharedCheck_6780_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_6683_);
                        leanh::lean_dec(v___x_6680_);
                        leanh::lean_dec_ref_known(v___x_6675_, 7);
                        leanh::lean_dec(v_declName_6661_);
                        leanh::lean_dec_ref(v___x_6660_);
                        leanh::lean_dec_ref(v___x_6659_);
                        leanh::lean_dec_ref(v___x_6658_);
                        leanh::lean_dec_ref(v___x_6657_);
                        leanh::lean_dec_ref(v___f_6656_);
                        leanh::lean_dec_ref(v_ext_6655_);
                        v_a_6781_ = leanh::lean_ctor_get(v___x_6684_, 0);
                        v_isSharedCheck_6788_ =
                            (!leanh::lean_is_exclusive(v___x_6684_)) as u8;
                        if v_isSharedCheck_6788_ == 0 {
                            v___x_6783_ = v___x_6684_;
                            v_isShared_6784_ = v_isSharedCheck_6788_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6781_);
                            leanh::lean_dec(v___x_6684_);
                            v___x_6783_ = leanh::lean_box(0);
                            v_isShared_6784_ = v_isSharedCheck_6788_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_6680_);
                    leanh::lean_dec_ref_known(v___x_6675_, 7);
                    leanh::lean_dec(v_declName_6661_);
                    leanh::lean_dec_ref(v___x_6660_);
                    leanh::lean_dec_ref(v___x_6659_);
                    leanh::lean_dec_ref(v___x_6658_);
                    leanh::lean_dec_ref(v___x_6657_);
                    leanh::lean_dec_ref(v___f_6656_);
                    leanh::lean_dec_ref(v_ext_6655_);
                    v_a_6789_ = leanh::lean_ctor_get(v___x_6681_, 0);
                    v_isSharedCheck_6796_ = (!leanh::lean_is_exclusive(v___x_6681_)) as u8;
                    if v_isSharedCheck_6796_ == 0 {
                        v___x_6791_ = v___x_6681_;
                        v_isShared_6792_ = v_isSharedCheck_6796_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6789_);
                        leanh::lean_dec(v___x_6681_);
                        v___x_6791_ = leanh::lean_box(0);
                        v_isShared_6792_ = v_isSharedCheck_6796_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6689_ = leanh::lean_box(0);
                leanh::lean_inc(v_declName_6661_);
                v___x_6717_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(
                    v_ext_6655_,
                    v_declName_6661_,
                    v_a_6685_,
                    v_attrKind_6663_,
                    v___x_6675_,
                    v___x_6680_,
                    v___y_6664_,
                    v___y_6665_,
                );
                if leanh::lean_obj_tag(v___x_6717_) == 0 {
                    leanh::lean_dec(v___x_6683_);
                    leanh::lean_dec_ref_known(v___x_6675_, 7);
                    leanh::lean_dec(v_declName_6661_);
                    leanh::lean_dec_ref(v___x_6660_);
                    leanh::lean_dec_ref(v___x_6659_);
                    leanh::lean_dec_ref(v___x_6658_);
                    leanh::lean_dec_ref(v___x_6657_);
                    leanh::lean_dec_ref(v___f_6656_);
                    v___y_6696_ = v___x_6717_;
                    state = 4;
                    continue;
                } else {
                    v_a_6718_ = leanh::lean_ctor_get(v___x_6717_, 0);
                    leanh::lean_inc(v_a_6718_);
                    v___x_6778_ = l_Lean_Exception_isInterrupt(v_a_6718_);
                    if v___x_6778_ == 0 {
                        v___x_6779_ = l_Lean_Exception_isRuntime(v_a_6718_);
                        v___y_6720_ = v___x_6779_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_6718_);
                        v___y_6720_ = v___x_6778_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6691_ = lean_st_ref_get(v___x_6680_);
                leanh::lean_dec(v___x_6680_);
                leanh::lean_dec(v___x_6691_);
                if v_isShared_6688_ == 0 {
                    leanh::lean_ctor_set(v___x_6687_, 0, v___x_6689_);
                    v___x_6693_ = v___x_6687_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6694_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 0, v___x_6689_);
                    v___x_6693_ = v_reuseFailAlloc_6694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6693_;
            }
            4 => {
                if leanh::lean_obj_tag(v___y_6696_) == 0 {
                    leanh::lean_dec_ref_known(v___y_6696_, 1);
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6687_);
                    leanh::lean_dec(v___x_6680_);
                    return v___y_6696_;
                }
            }
            5 => {
                leanh::lean_inc(v___y_6665_);
                leanh::lean_inc_ref(v___y_6664_);
                leanh::lean_inc(v___x_6680_);
                v___x_6698_ = leanh::lean_apply_6(
                    v___f_6656_,
                    v___x_6689_,
                    v___x_6675_,
                    v___x_6680_,
                    v___y_6664_,
                    v___y_6665_,
                    leanh::lean_box(0),
                );
                v___y_6696_ = v___x_6698_;
                state = 4;
                continue;
            }
            6 => {
                if v___y_6704_ == 0 {
                    leanh::lean_dec_ref(v___y_6702_);
                    v_hasTrace_6705_ = leanh::lean_ctor_get_uint8(
                        v___y_6700_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6705_ == 0 {
                        leanh::lean_dec_ref(v___y_6701_);
                        leanh::lean_dec_ref(v___x_6659_);
                        leanh::lean_dec_ref(v___x_6658_);
                        leanh::lean_dec_ref(v___x_6657_);
                        state = 5;
                        continue;
                    } else {
                        v___x_6706_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
                        v___x_6707_ =
                            l_Lean_Name_mkStr4(v___x_6657_, v___x_6658_, v___x_6659_, v___x_6706_);
                        v___x_6708_ =
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11;
                        leanh::lean_inc(v___x_6707_);
                        v___x_6709_ = l_Lean_Name_append(v___x_6708_, v___x_6707_);
                        v___x_6710_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___y_6703_,
                            v___y_6700_,
                            v___x_6709_,
                        );
                        leanh::lean_dec(v___x_6709_);
                        if v___x_6710_ == 0 {
                            leanh::lean_dec(v___x_6707_);
                            leanh::lean_dec_ref(v___y_6701_);
                            state = 5;
                            continue;
                        } else {
                            v___x_6711_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13);
                            v___x_6712_ = l_Lean_Exception_toMessageData(v___y_6701_);
                            v___x_6713_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6713_, 0, v___x_6711_);
                            leanh::lean_ctor_set(v___x_6713_, 1, v___x_6712_);
                            v___x_6714_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v___x_6707_, v___x_6713_, v___x_6675_, v___x_6680_, v___y_6664_, v___y_6665_);
                            if leanh::lean_obj_tag(v___x_6714_) == 0 {
                                v_a_6715_ = leanh::lean_ctor_get(v___x_6714_, 0);
                                leanh::lean_inc(v_a_6715_);
                                leanh::lean_dec_ref_known(v___x_6714_, 1);
                                leanh::lean_inc(v___y_6665_);
                                leanh::lean_inc_ref(v___y_6664_);
                                leanh::lean_inc(v___x_6680_);
                                v___x_6716_ = leanh::lean_apply_6(
                                    v___f_6656_,
                                    v_a_6715_,
                                    v___x_6675_,
                                    v___x_6680_,
                                    v___y_6664_,
                                    v___y_6665_,
                                    leanh::lean_box(0),
                                );
                                v___y_6696_ = v___x_6716_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v___x_6675_, 7);
                                leanh::lean_dec_ref(v___f_6656_);
                                v___y_6696_ = v___x_6714_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6701_);
                    leanh::lean_del_object(v___x_6687_);
                    leanh::lean_dec(v___x_6680_);
                    leanh::lean_dec_ref_known(v___x_6675_, 7);
                    leanh::lean_dec_ref(v___x_6659_);
                    leanh::lean_dec_ref(v___x_6658_);
                    leanh::lean_dec_ref(v___x_6657_);
                    leanh::lean_dec_ref(v___f_6656_);
                    return v___y_6702_;
                }
            }
            7 => {
                if v___y_6720_ == 0 {
                    v_isSharedCheck_6776_ = (!leanh::lean_is_exclusive(v___x_6717_)) as u8;
                    if v_isSharedCheck_6776_ == 0 {
                        v_unused_6777_ = leanh::lean_ctor_get(v___x_6717_, 0);
                        leanh::lean_dec(v_unused_6777_);
                        v___x_6722_ = v___x_6717_;
                        v_isShared_6723_ = v_isSharedCheck_6776_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6717_);
                        v___x_6722_ = leanh::lean_box(0);
                        v_isShared_6723_ = v_isSharedCheck_6776_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6683_);
                    leanh::lean_dec_ref_known(v___x_6675_, 7);
                    leanh::lean_dec(v_declName_6661_);
                    leanh::lean_dec_ref(v___x_6660_);
                    leanh::lean_dec_ref(v___x_6659_);
                    leanh::lean_dec_ref(v___x_6658_);
                    leanh::lean_dec_ref(v___x_6657_);
                    leanh::lean_dec_ref(v___f_6656_);
                    v___y_6696_ = v___x_6717_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_6724_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
                v___x_6725_ = l_Lean_getBuiltinAttributeImpl(v___x_6724_);
                if leanh::lean_obj_tag(v___x_6725_) == 0 {
                    leanh::lean_del_object(v___x_6722_);
                    v_a_6726_ = leanh::lean_ctor_get(v___x_6725_, 0);
                    leanh::lean_inc(v_a_6726_);
                    leanh::lean_dec_ref_known(v___x_6725_, 1);
                    v_options_6727_ = leanh::lean_ctor_get(v___y_6664_, 2);
                    v_ref_6728_ = leanh::lean_ctor_get(v___y_6664_, 5);
                    v_quotContext_6729_ = leanh::lean_ctor_get(v___y_6664_, 10);
                    v_currMacroScope_6730_ = leanh::lean_ctor_get(v___y_6664_, 11);
                    v_inheritedTraceOptions_6731_ = leanh::lean_ctor_get(v___y_6664_, 13);
                    v___x_6732_ = l_Lean_SourceInfo_fromRef(v_ref_6728_, v___y_6720_);
                    v___x_6733_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14,
                    );
                    leanh::lean_inc(v_currMacroScope_6730_);
                    leanh::lean_inc(v_quotContext_6729_);
                    v___x_6734_ = l_Lean_addMacroScope(
                        v_quotContext_6729_,
                        v___x_6724_,
                        v_currMacroScope_6730_,
                    );
                    v___x_6735_ = leanh::lean_box(0);
                    leanh::lean_inc(v___x_6732_);
                    v___x_6736_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_6736_, 0, v___x_6732_);
                    leanh::lean_ctor_set(v___x_6736_, 1, v___x_6733_);
                    leanh::lean_ctor_set(v___x_6736_, 2, v___x_6734_);
                    leanh::lean_ctor_set(v___x_6736_, 3, v___x_6735_);
                    v_add_6737_ = leanh::lean_ctor_get(v_a_6726_, 1);
                    v_isSharedCheck_6758_ = (!leanh::lean_is_exclusive(v_a_6726_)) as u8;
                    if v_isSharedCheck_6758_ == 0 {
                        v_unused_6759_ = leanh::lean_ctor_get(v_a_6726_, 2);
                        leanh::lean_dec(v_unused_6759_);
                        v_unused_6760_ = leanh::lean_ctor_get(v_a_6726_, 0);
                        leanh::lean_dec(v_unused_6760_);
                        v___x_6739_ = v_a_6726_;
                        v_isShared_6740_ = v_isSharedCheck_6758_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_add_6737_);
                        leanh::lean_dec(v_a_6726_);
                        v___x_6739_ = leanh::lean_box(0);
                        v_isShared_6740_ = v_isSharedCheck_6758_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6687_);
                    leanh::lean_dec(v___x_6683_);
                    leanh::lean_dec(v___x_6680_);
                    leanh::lean_dec_ref_known(v___x_6675_, 7);
                    leanh::lean_dec(v_declName_6661_);
                    leanh::lean_dec_ref(v___x_6660_);
                    leanh::lean_dec_ref(v___x_6659_);
                    leanh::lean_dec_ref(v___x_6658_);
                    leanh::lean_dec_ref(v___x_6657_);
                    leanh::lean_dec_ref(v___f_6656_);
                    v_a_6761_ = leanh::lean_ctor_get(v___x_6725_, 0);
                    v_isSharedCheck_6775_ = (!leanh::lean_is_exclusive(v___x_6725_)) as u8;
                    if v_isSharedCheck_6775_ == 0 {
                        v___x_6763_ = v___x_6725_;
                        v_isShared_6764_ = v_isSharedCheck_6775_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6761_);
                        leanh::lean_dec(v___x_6725_);
                        v___x_6763_ = leanh::lean_box(0);
                        v_isShared_6764_ = v_isSharedCheck_6775_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_6741_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16;
                v___x_6742_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17,
                );
                leanh::lean_inc(v___x_6732_);
                if v_isShared_6740_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6739_, 1);
                    leanh::lean_ctor_set(v___x_6739_, 2, v___x_6742_);
                    leanh::lean_ctor_set(v___x_6739_, 1, v___x_6741_);
                    leanh::lean_ctor_set(v___x_6739_, 0, v___x_6732_);
                    v___x_6744_ = v___x_6739_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 0, v___x_6732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 1, v___x_6741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 2, v___x_6742_);
                    v___x_6744_ = v_reuseFailAlloc_6757_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6745_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18;
                v___x_6746_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
                v___x_6747_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19;
                v___x_6748_ =
                    l_Lean_Name_mkStr4(v___x_6660_, v___x_6745_, v___x_6746_, v___x_6747_);
                v___x_6749_ =
                    l_Lean_Syntax_node2(v___x_6732_, v___x_6748_, v___x_6736_, v___x_6744_);
                v___x_6750_ = leanh::lean_unsigned_to_nat(3);
                v___x_6751_ = l_Lean_Syntax_setArg(v___x_6749_, v___x_6750_, v___x_6683_);
                v___x_6752_ = leanh::lean_box((v_attrKind_6663_) as usize);
                leanh::lean_inc(v___y_6665_);
                leanh::lean_inc_ref(v___y_6664_);
                v___x_6753_ = leanh::lean_apply_6(
                    v_add_6737_,
                    v_declName_6661_,
                    v___x_6751_,
                    v___x_6752_,
                    v___y_6664_,
                    v___y_6665_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6753_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6753_, 1);
                    leanh::lean_dec_ref_known(v___x_6675_, 7);
                    leanh::lean_dec_ref(v___x_6659_);
                    leanh::lean_dec_ref(v___x_6658_);
                    leanh::lean_dec_ref(v___x_6657_);
                    leanh::lean_dec_ref(v___f_6656_);
                    state = 2;
                    continue;
                } else {
                    v_a_6754_ = leanh::lean_ctor_get(v___x_6753_, 0);
                    leanh::lean_inc(v_a_6754_);
                    v___x_6755_ = l_Lean_Exception_isInterrupt(v_a_6754_);
                    if v___x_6755_ == 0 {
                        leanh::lean_inc(v_a_6754_);
                        v___x_6756_ = l_Lean_Exception_isRuntime(v_a_6754_);
                        v___y_6700_ = v_options_6727_;
                        v___y_6701_ = v_a_6754_;
                        v___y_6702_ = v___x_6753_;
                        v___y_6703_ = v_inheritedTraceOptions_6731_;
                        v___y_6704_ = v___x_6756_;
                        state = 6;
                        continue;
                    } else {
                        v___y_6700_ = v_options_6727_;
                        v___y_6701_ = v_a_6754_;
                        v___y_6702_ = v___x_6753_;
                        v___y_6703_ = v_inheritedTraceOptions_6731_;
                        v___y_6704_ = v___x_6755_;
                        state = 6;
                        continue;
                    }
                }
            }
            11 => {
                v_ref_6765_ = leanh::lean_ctor_get(v___y_6664_, 5);
                v___x_6766_ = lean_io_error_to_string(v_a_6761_);
                if v_isShared_6723_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6722_, 3);
                    leanh::lean_ctor_set(v___x_6722_, 0, v___x_6766_);
                    v___x_6768_ = v___x_6722_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6774_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6774_, 0, v___x_6766_);
                    v___x_6768_ = v_reuseFailAlloc_6774_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6769_ = l_Lean_MessageData_ofFormat(v___x_6768_);
                leanh::lean_inc(v_ref_6765_);
                v___x_6770_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6770_, 0, v_ref_6765_);
                leanh::lean_ctor_set(v___x_6770_, 1, v___x_6769_);
                if v_isShared_6764_ == 0 {
                    leanh::lean_ctor_set(v___x_6763_, 0, v___x_6770_);
                    v___x_6772_ = v___x_6763_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6773_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 0, v___x_6770_);
                    v___x_6772_ = v_reuseFailAlloc_6773_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6772_;
            }
            14 => {
                if v_isShared_6784_ == 0 {
                    v___x_6786_ = v___x_6783_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6787_, 0, v_a_6781_);
                    v___x_6786_ = v_reuseFailAlloc_6787_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6786_;
            }
            16 => {
                if v_isShared_6792_ == 0 {
                    v___x_6794_ = v___x_6791_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6795_, 0, v_a_6789_);
                    v___x_6794_ = v_reuseFailAlloc_6795_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed(
    mut v___x_6797_: *mut leanh::LeanObject,
    mut v_ext_6798_: *mut leanh::LeanObject,
    mut v___f_6799_: *mut leanh::LeanObject,
    mut v___x_6800_: *mut leanh::LeanObject,
    mut v___x_6801_: *mut leanh::LeanObject,
    mut v___x_6802_: *mut leanh::LeanObject,
    mut v___x_6803_: *mut leanh::LeanObject,
    mut v_declName_6804_: *mut leanh::LeanObject,
    mut v_stx_6805_: *mut leanh::LeanObject,
    mut v_attrKind_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
    mut v___y_6808_: *mut leanh::LeanObject,
    mut v___y_6809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_attrKind_boxed_6810_: u8 = 0;
    let mut v_res_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6810_ = (leanh::lean_unbox(v_attrKind_6806_) as u8);
    v_res_6811_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(
        v___x_6797_,
        v_ext_6798_,
        v___f_6799_,
        v___x_6800_,
        v___x_6801_,
        v___x_6802_,
        v___x_6803_,
        v_declName_6804_,
        v_stx_6805_,
        v_attrKind_boxed_6810_,
        v___y_6807_,
        v___y_6808_,
    );
    leanh::lean_dec(v___y_6808_);
    leanh::lean_dec_ref(v___y_6807_);
    leanh::lean_dec(v_stx_6805_);
    return v_res_6811_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(
    mut v_msgData_6812_: *mut leanh::LeanObject,
    mut v___y_6813_: *mut leanh::LeanObject,
    mut v___y_6814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6816_ = lean_st_ref_get(v___y_6814_);
    v_env_6817_ = leanh::lean_ctor_get(v___x_6816_, 0);
    leanh::lean_inc_ref(v_env_6817_);
    leanh::lean_dec(v___x_6816_);
    v_options_6818_ = leanh::lean_ctor_get(v___y_6813_, 2);
    v___x_6819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
    v___x_6820_ = leanh::lean_unsigned_to_nat(32);
    v___x_6821_ = lean_mk_empty_array_with_capacity(v___x_6820_);
    leanh::lean_dec_ref(v___x_6821_);
    v___x_6822_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
    leanh::lean_inc_ref(v_options_6818_);
    v___x_6823_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6823_, 0, v_env_6817_);
    leanh::lean_ctor_set(v___x_6823_, 1, v___x_6819_);
    leanh::lean_ctor_set(v___x_6823_, 2, v___x_6822_);
    leanh::lean_ctor_set(v___x_6823_, 3, v_options_6818_);
    v___x_6824_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6824_, 0, v___x_6823_);
    leanh::lean_ctor_set(v___x_6824_, 1, v_msgData_6812_);
    v___x_6825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6825_, 0, v___x_6824_);
    return v___x_6825_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(
    mut v_msgData_6826_: *mut leanh::LeanObject,
    mut v___y_6827_: *mut leanh::LeanObject,
    mut v___y_6828_: *mut leanh::LeanObject,
    mut v___y_6829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6830_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msgData_6826_, v___y_6827_, v___y_6828_);
    leanh::lean_dec(v___y_6828_);
    leanh::lean_dec_ref(v___y_6827_);
    return v_res_6830_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
    mut v_msg_6831_: *mut leanh::LeanObject,
    mut v___y_6832_: *mut leanh::LeanObject,
    mut v___y_6833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6840_: u8 = 0;
    let mut v___x_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6835_ = leanh::lean_ctor_get(v___y_6832_, 5);
                v___x_6836_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msg_6831_, v___y_6832_, v___y_6833_);
                v_a_6837_ = leanh::lean_ctor_get(v___x_6836_, 0);
                v_isSharedCheck_6845_ = (!leanh::lean_is_exclusive(v___x_6836_)) as u8;
                if v_isSharedCheck_6845_ == 0 {
                    v___x_6839_ = v___x_6836_;
                    v_isShared_6840_ = v_isSharedCheck_6845_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6837_);
                    leanh::lean_dec(v___x_6836_);
                    v___x_6839_ = leanh::lean_box(0);
                    v_isShared_6840_ = v_isSharedCheck_6845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_6835_);
                v___x_6841_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6841_, 0, v_ref_6835_);
                leanh::lean_ctor_set(v___x_6841_, 1, v_a_6837_);
                if v_isShared_6840_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6839_, 1);
                    leanh::lean_ctor_set(v___x_6839_, 0, v___x_6841_);
                    v___x_6843_ = v___x_6839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 0, v___x_6841_);
                    v___x_6843_ = v_reuseFailAlloc_6844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg___boxed(
    mut v_msg_6846_: *mut leanh::LeanObject,
    mut v___y_6847_: *mut leanh::LeanObject,
    mut v___y_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6850_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
            v_msg_6846_,
            v___y_6847_,
            v___y_6848_,
        );
    leanh::lean_dec(v___y_6848_);
    leanh::lean_dec_ref(v___y_6847_);
    return v_res_6850_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6852_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0;
    v___x_6853_ = l_Lean_stringToMessageData(v___x_6852_);
    return v___x_6853_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6855_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2;
    v___x_6856_ = l_Lean_stringToMessageData(v___x_6855_);
    return v___x_6856_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(
    mut v___x_6857_: *mut leanh::LeanObject,
    mut v_decl_6858_: *mut leanh::LeanObject,
    mut v___y_6859_: *mut leanh::LeanObject,
    mut v___y_6860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6862_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1,
    );
    v___x_6863_ = l_Lean_MessageData_ofName(v___x_6857_);
    v___x_6864_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6864_, 0, v___x_6862_);
    leanh::lean_ctor_set(v___x_6864_, 1, v___x_6863_);
    v___x_6865_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3,
    );
    v___x_6866_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6866_, 0, v___x_6864_);
    leanh::lean_ctor_set(v___x_6866_, 1, v___x_6865_);
    v___x_6867_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
            v___x_6866_,
            v___y_6859_,
            v___y_6860_,
        );
    return v___x_6867_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(
    mut v___x_6868_: *mut leanh::LeanObject,
    mut v_decl_6869_: *mut leanh::LeanObject,
    mut v___y_6870_: *mut leanh::LeanObject,
    mut v___y_6871_: *mut leanh::LeanObject,
    mut v___y_6872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6873_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(
        v___x_6868_,
        v_decl_6869_,
        v___y_6870_,
        v___y_6871_,
    );
    leanh::lean_dec(v___y_6871_);
    leanh::lean_dec_ref(v___y_6870_);
    leanh::lean_dec(v_decl_6869_);
    return v_res_6873_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(
    mut v_ext_6894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6895_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0;
    v___x_6896_ = leanh::lean_box(1);
    v___x_6897_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_6898_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_6899_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_6900_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___f_6901_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed as *mut core::ffi::c_void,
        13,
        7,
    );
    leanh::lean_closure_set(v___f_6901_, 0, v___x_6896_);
    leanh::lean_closure_set(v___f_6901_, 1, v_ext_6894_);
    leanh::lean_closure_set(v___f_6901_, 2, v___f_6895_);
    leanh::lean_closure_set(v___f_6901_, 3, v___x_6898_);
    leanh::lean_closure_set(v___f_6901_, 4, v___x_6899_);
    leanh::lean_closure_set(v___f_6901_, 5, v___x_6900_);
    leanh::lean_closure_set(v___f_6901_, 6, v___x_6897_);
    v___f_6902_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5;
    v___x_6903_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7;
    v___x_6904_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6904_, 0, v___x_6903_);
    leanh::lean_ctor_set(v___x_6904_, 1, v___f_6901_);
    leanh::lean_ctor_set(v___x_6904_, 2, v___f_6902_);
    return v___x_6904_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(
    mut v_00_u03b1_6905_: *mut leanh::LeanObject,
    mut v_msg_6906_: *mut leanh::LeanObject,
    mut v___y_6907_: *mut leanh::LeanObject,
    mut v___y_6908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6910_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
            v_msg_6906_,
            v___y_6907_,
            v___y_6908_,
        );
    return v___x_6910_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(
    mut v_00_u03b1_6911_: *mut leanh::LeanObject,
    mut v_msg_6912_: *mut leanh::LeanObject,
    mut v___y_6913_: *mut leanh::LeanObject,
    mut v___y_6914_: *mut leanh::LeanObject,
    mut v___y_6915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6916_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(
        v_00_u03b1_6911_,
        v_msg_6912_,
        v___y_6913_,
        v___y_6914_,
    );
    leanh::lean_dec(v___y_6914_);
    leanh::lean_dec_ref(v___y_6913_);
    return v_res_6916_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6917_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
    v___x_6918_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(v___x_6917_);
    return v___x_6918_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6920_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_);
    v___x_6921_ = l_Lean_registerBuiltinAttribute(v___x_6920_);
    return v___x_6921_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(
    mut v_a_6922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6923_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
    return v_res_6923_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(
    mut v_ext_6924_: *mut leanh::LeanObject,
    mut v_a_6925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6927_ = lean_st_ref_get(v_a_6925_);
    v_ext_6928_ = leanh::lean_ctor_get(v_ext_6924_, 1);
    v_toEnvExtension_6929_ = leanh::lean_ctor_get(v_ext_6928_, 0);
    v_env_6930_ = leanh::lean_ctor_get(v___x_6927_, 0);
    leanh::lean_inc_ref(v_env_6930_);
    leanh::lean_dec(v___x_6927_);
    v_asyncMode_6931_ = leanh::lean_ctor_get(v_toEnvExtension_6929_, 2);
    v___x_6932_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
    v___x_6933_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_6932_,
        v_ext_6924_,
        v_env_6930_,
        v_asyncMode_6931_,
    );
    v___x_6934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6934_, 0, v___x_6933_);
    return v___x_6934_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(
    mut v_ext_6935_: *mut leanh::LeanObject,
    mut v_a_6936_: *mut leanh::LeanObject,
    mut v_a_6937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6938_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_6935_, v_a_6936_);
    leanh::lean_dec(v_a_6936_);
    leanh::lean_dec_ref(v_ext_6935_);
    return v_res_6938_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(
    mut v_ext_6939_: *mut leanh::LeanObject,
    mut v_a_6940_: *mut leanh::LeanObject,
    mut v_a_6941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6943_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_6939_, v_a_6941_);
    return v___x_6943_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(
    mut v_ext_6944_: *mut leanh::LeanObject,
    mut v_a_6945_: *mut leanh::LeanObject,
    mut v_a_6946_: *mut leanh::LeanObject,
    mut v_a_6947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6948_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_6944_, v_a_6945_, v_a_6946_);
    leanh::lean_dec(v_a_6946_);
    leanh::lean_dec_ref(v_a_6945_);
    leanh::lean_dec_ref(v_ext_6944_);
    return v_res_6948_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(
    mut v_a_6949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6951_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
    v___x_6952_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_6951_, v_a_6949_);
    return v___x_6952_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(
    mut v_a_6953_: *mut leanh::LeanObject,
    mut v_a_6954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6955_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_6953_);
    leanh::lean_dec(v_a_6953_);
    return v_res_6955_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(
    mut v_a_6956_: *mut leanh::LeanObject,
    mut v_a_6957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6959_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_6957_);
    return v___x_6959_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(
    mut v_a_6960_: *mut leanh::LeanObject,
    mut v_a_6961_: *mut leanh::LeanObject,
    mut v_a_6962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6963_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_6960_, v_a_6961_);
    leanh::lean_dec(v_a_6961_);
    leanh::lean_dec_ref(v_a_6960_);
    return v_res_6963_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(
    mut v_x_6964_: *mut leanh::LeanObject,
    mut v___y_6965_: *mut leanh::LeanObject,
    mut v___y_6966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6968_ = leanh::lean_box(0);
    v___x_6969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6969_, 0, v___x_6968_);
    return v___x_6969_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(
    mut v_x_6970_: *mut leanh::LeanObject,
    mut v___y_6971_: *mut leanh::LeanObject,
    mut v___y_6972_: *mut leanh::LeanObject,
    mut v___y_6973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6974_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(v_x_6970_, v___y_6971_, v___y_6972_);
    leanh::lean_dec(v___y_6972_);
    leanh::lean_dec_ref(v___y_6971_);
    leanh::lean_dec(v_x_6970_);
    return v_res_6974_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: u8 = 0;
    let mut v___x_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6989_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6990_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6991_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6992_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6993_ = 0;
    v___x_6994_ = leanh::lean_box(2);
    v___x_6995_ = l_Lean_registerTagAttribute(
        v___x_6990_,
        v___x_6991_,
        v___f_6989_,
        v___x_6992_,
        v___x_6993_,
        v___x_6994_,
    );
    return v___x_6995_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(
    mut v_a_6996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6997_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
    return v_res_6997_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(
    mut v_env_6998_: *mut leanh::LeanObject,
    mut v_ty_6999_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7000_ = l_Lean_Expr_getAppFn(v_ty_6999_);
    if leanh::lean_obj_tag(v___x_7000_) == 4 {
        let mut v_declName_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7003_: u8 = 0;
        v_declName_7001_ = leanh::lean_ctor_get(v___x_7000_, 0);
        leanh::lean_inc(v_declName_7001_);
        leanh::lean_dec_ref_known(v___x_7000_, 2);
        v___x_7002_ = l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
        v___x_7003_ = l_Lean_TagAttribute_hasTag(v___x_7002_, v_env_6998_, v_declName_7001_);
        return v___x_7003_;
    } else {
        let mut v___x_7004_: u8 = 0;
        leanh::lean_dec_ref(v___x_7000_);
        leanh::lean_dec_ref(v_env_6998_);
        v___x_7004_ = 0;
        return v___x_7004_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(
    mut v_env_7005_: *mut leanh::LeanObject,
    mut v_ty_7006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7007_: u8 = 0;
    let mut v_r_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7007_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_7005_, v_ty_7006_);
    leanh::lean_dec_ref(v_ty_7006_);
    v_r_7008_ = leanh::lean_box((v_res_7007_) as usize);
    return v_r_7008_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Attr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt);
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default();
    leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default,
    );
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem);
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default();
    leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default,
    );
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems);
    l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig);
    l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt = _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Do_SpecAttr_specAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specAttr);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Attr(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Attr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Attr(builtin);
}