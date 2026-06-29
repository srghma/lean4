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
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 112, 101, 99, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17186385980065365684 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6272605754531080404 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8329279028482663286 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5409699204079762053 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14659826576719934041 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18416200079748401721 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5290553688444538652 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1661666541244903741 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15779238732938891787 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2811310707656781194 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8663997493493226818 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 112, 101, 99, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10914722979873168125 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17038327469269433204 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6906709583315380253 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4219124626137388200 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4322195018672482898 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9557857920321765335 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3768395763851350643 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10035844726815915179 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1315642830 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5914060295816363643 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10159048236521340864 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6137995315809427492 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15422401092800951869 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 118, 99, 103, 101, 110, 95, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12870045445243962497 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 105, 110, 116, 101, 114, 110, 97, 108, 108, 121, 32, 117, 115, 101, 100, 32, 98, 121, 32, 96, 109, 118, 99, 103, 101, 110, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 118, 99, 103, 101, 110, 83, 105, 109, 112, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8359407510875696518 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6847237493982576655 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0: u64 = 0;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
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
        83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 108, 111, 99, 97, 108, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
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
        83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 115, 116, 120, 32, 95, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,8614124190858717794 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 105, 110, 100, 32, 111, 102, 32, 115, 112, 101, 99, 32, 116, 104, 101, 111, 114, 101, 109, 59, 32, 110, 111, 116, 32, 97, 32, 116, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,11963640885769744415 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 111, 115, 116, 83, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 114, 103, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,6471916472876379905 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,16115802990853135195 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 39, 115, 112, 101, 99, 39, 44, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14904224527309176076 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_specAttr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<83> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut crate::leanh::LeanObject,
        72621647814721793 as *mut crate::leanh::LeanObject,
        65793 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1: u64 = 0;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__15_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8359407510875696518 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11196778731259658883 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__3_value)
            as *mut crate::leanh::LeanObject,
        9363898782269073664 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value:
    crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__6_value)
            as *mut crate::leanh::LeanObject,
        1 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [115, 112, 101, 99, 95, 105, 110, 118, 97, 114, 105, 97, 110, 116, 95, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5551193628827022521 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [109, 97, 114, 107, 115, 32, 97, 32, 116, 121, 112, 101, 32, 97, 115, 32, 97, 110, 32, 105, 110, 118, 97, 114, 105, 97, 110, 116, 32, 116, 121, 112, 101, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 109, 118, 99, 103, 101, 110, 96, 32, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [115, 112, 101, 99, 73, 110, 118, 97, 114, 105, 97, 110, 116, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8359407510875696518 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10016391191665048052 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_3593_ = 0;
    v___x_3594_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_3595_ = l_Lean_registerTraceClass(v___x_3592_, v___x_3593_, v___x_3594_);
    return v___x_3595_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2____boxed(
    mut v_a_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
    return v_res_3597_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3611_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_3612_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_3613_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_3614_ = l_Lean_Meta_registerSimpAttr(v___x_3611_, v___x_3612_, v___x_3613_);
    return v___x_3614_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2____boxed(
    mut v_a_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
    return v_res_3616_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(
    mut v_a_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt;
    v___x_3620_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3619_, v_a_3617_);
    return v___x_3620_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg___boxed(
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3623_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(v_a_3621_);
    crate::leanh::lean_dec(v_a_3621_);
    return v_res_3623_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(
    mut v_a_3624_: *mut crate::leanh::LeanObject,
    mut v_a_3625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___redArg(v_a_3625_);
    return v___x_3627_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed(
    mut v_a_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems(v_a_3628_, v_a_3629_);
    crate::leanh::lean_dec(v_a_3629_);
    crate::leanh::lean_dec_ref(v_a_3628_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(
    mut v_x_3632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3632_) {
        0 => {
            let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3633_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3633_;
        }
        1 => {
            let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3634_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3634_;
        }
        _ => {
            let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3635_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3635_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx___boxed(
    mut v_x_3636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3637_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorIdx(v_x_3636_);
    crate::leanh::lean_dec_ref(v_x_3636_);
    return v_res_3637_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(
    mut v_t_3638_: *mut crate::leanh::LeanObject,
    mut v_k_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3638_) == 2 {
        let mut v_id_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_proof_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_id_3640_ = crate::leanh::lean_ctor_get(v_t_3638_, 0);
        crate::leanh::lean_inc(v_id_3640_);
        v_ref_3641_ = crate::leanh::lean_ctor_get(v_t_3638_, 1);
        crate::leanh::lean_inc(v_ref_3641_);
        v_proof_3642_ = crate::leanh::lean_ctor_get(v_t_3638_, 2);
        crate::leanh::lean_inc_ref(v_proof_3642_);
        crate::leanh::lean_dec_ref_known(v_t_3638_, 3);
        v___x_3643_ = crate::leanh::lean_apply_3(v_k_3639_, v_id_3640_, v_ref_3641_, v_proof_3642_);
        return v___x_3643_;
    } else {
        let mut v_declName_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_3644_ = crate::leanh::lean_ctor_get(v_t_3638_, 0);
        crate::leanh::lean_inc(v_declName_3644_);
        crate::leanh::lean_dec_ref(v_t_3638_);
        v___x_3645_ = crate::leanh::lean_apply_1(v_k_3639_, v_declName_3644_);
        return v___x_3645_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(
    mut v_motive_3646_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3647_: *mut crate::leanh::LeanObject,
    mut v_t_3648_: *mut crate::leanh::LeanObject,
    mut v_h_3649_: *mut crate::leanh::LeanObject,
    mut v_k_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3651_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3648_, v_k_3650_);
    return v___x_3651_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___boxed(
    mut v_motive_3652_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3653_: *mut crate::leanh::LeanObject,
    mut v_t_3654_: *mut crate::leanh::LeanObject,
    mut v_h_3655_: *mut crate::leanh::LeanObject,
    mut v_k_3656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim(
        v_motive_3652_,
        v_ctorIdx_3653_,
        v_t_3654_,
        v_h_3655_,
        v_k_3656_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3653_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim___redArg(
    mut v_t_3658_: *mut crate::leanh::LeanObject,
    mut v_global_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3660_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3658_, v_global_3659_);
    return v___x_3660_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_global_elim(
    mut v_motive_3661_: *mut crate::leanh::LeanObject,
    mut v_t_3662_: *mut crate::leanh::LeanObject,
    mut v_h_3663_: *mut crate::leanh::LeanObject,
    mut v_global_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3662_, v_global_3664_);
    return v___x_3665_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim___redArg(
    mut v_t_3666_: *mut crate::leanh::LeanObject,
    mut v_local_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3668_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3666_, v_local_3667_);
    return v___x_3668_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_local_elim(
    mut v_motive_3669_: *mut crate::leanh::LeanObject,
    mut v_t_3670_: *mut crate::leanh::LeanObject,
    mut v_h_3671_: *mut crate::leanh::LeanObject,
    mut v_local_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3670_, v_local_3672_);
    return v___x_3673_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim___redArg(
    mut v_t_3674_: *mut crate::leanh::LeanObject,
    mut v_stx_3675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3676_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3674_, v_stx_3675_);
    return v___x_3676_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_stx_elim(
    mut v_motive_3677_: *mut crate::leanh::LeanObject,
    mut v_t_3678_: *mut crate::leanh::LeanObject,
    mut v_h_3679_: *mut crate::leanh::LeanObject,
    mut v_stx_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3681_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ctorElim___redArg(v_t_3678_, v_stx_3680_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
    mut v_x_3686_: *mut crate::leanh::LeanObject,
    mut v_x_3687_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_3686_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_3687_) == 0 {
                let mut v_declName_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_declName_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3690_: u8 = 0;
                v_declName_3688_ = crate::leanh::lean_ctor_get(v_x_3686_, 0);
                crate::leanh::lean_inc(v_declName_3688_);
                crate::leanh::lean_dec_ref_known(v_x_3686_, 1);
                v_declName_3689_ = crate::leanh::lean_ctor_get(v_x_3687_, 0);
                crate::leanh::lean_inc(v_declName_3689_);
                crate::leanh::lean_dec_ref_known(v_x_3687_, 1);
                v___x_3690_ = lean_name_eq(v_declName_3688_, v_declName_3689_);
                crate::leanh::lean_dec(v_declName_3689_);
                crate::leanh::lean_dec(v_declName_3688_);
                return v___x_3690_;
            } else {
                let mut v___x_3691_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v_x_3686_, 1);
                crate::leanh::lean_dec_ref(v_x_3687_);
                v___x_3691_ = 0;
                return v___x_3691_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_3687_) == 1 {
                let mut v_fvarId_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_fvarId_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3694_: u8 = 0;
                v_fvarId_3692_ = crate::leanh::lean_ctor_get(v_x_3686_, 0);
                crate::leanh::lean_inc(v_fvarId_3692_);
                crate::leanh::lean_dec_ref_known(v_x_3686_, 1);
                v_fvarId_3693_ = crate::leanh::lean_ctor_get(v_x_3687_, 0);
                crate::leanh::lean_inc(v_fvarId_3693_);
                crate::leanh::lean_dec_ref_known(v_x_3687_, 1);
                v___x_3694_ = l_Lean_instBEqFVarId_beq(v_fvarId_3692_, v_fvarId_3693_);
                crate::leanh::lean_dec(v_fvarId_3693_);
                crate::leanh::lean_dec(v_fvarId_3692_);
                return v___x_3694_;
            } else {
                let mut v___x_3695_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v_x_3686_, 1);
                crate::leanh::lean_dec_ref(v_x_3687_);
                v___x_3695_ = 0;
                return v___x_3695_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_3687_) == 2 {
                let mut v_id_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_proof_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_id_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_proof_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3702_: u8 = 0;
                v_id_3696_ = crate::leanh::lean_ctor_get(v_x_3686_, 0);
                crate::leanh::lean_inc(v_id_3696_);
                v_ref_3697_ = crate::leanh::lean_ctor_get(v_x_3686_, 1);
                crate::leanh::lean_inc(v_ref_3697_);
                v_proof_3698_ = crate::leanh::lean_ctor_get(v_x_3686_, 2);
                crate::leanh::lean_inc_ref(v_proof_3698_);
                crate::leanh::lean_dec_ref_known(v_x_3686_, 3);
                v_id_3699_ = crate::leanh::lean_ctor_get(v_x_3687_, 0);
                crate::leanh::lean_inc(v_id_3699_);
                v_ref_3700_ = crate::leanh::lean_ctor_get(v_x_3687_, 1);
                crate::leanh::lean_inc(v_ref_3700_);
                v_proof_3701_ = crate::leanh::lean_ctor_get(v_x_3687_, 2);
                crate::leanh::lean_inc_ref(v_proof_3701_);
                crate::leanh::lean_dec_ref_known(v_x_3687_, 3);
                v___x_3702_ = lean_name_eq(v_id_3696_, v_id_3699_);
                crate::leanh::lean_dec(v_id_3699_);
                crate::leanh::lean_dec(v_id_3696_);
                if v___x_3702_ == 0 {
                    crate::leanh::lean_dec_ref(v_proof_3701_);
                    crate::leanh::lean_dec(v_ref_3700_);
                    crate::leanh::lean_dec_ref(v_proof_3698_);
                    crate::leanh::lean_dec(v_ref_3697_);
                    return v___x_3702_;
                } else {
                    let mut v___x_3703_: u8 = 0;
                    v___x_3703_ = l_Lean_Syntax_structEq(v_ref_3697_, v_ref_3700_);
                    if v___x_3703_ == 0 {
                        crate::leanh::lean_dec_ref(v_proof_3701_);
                        crate::leanh::lean_dec_ref(v_proof_3698_);
                        return v___x_3703_;
                    } else {
                        let mut v___x_3704_: u8 = 0;
                        v___x_3704_ = lean_expr_eqv(v_proof_3698_, v_proof_3701_);
                        crate::leanh::lean_dec_ref(v_proof_3701_);
                        crate::leanh::lean_dec_ref(v_proof_3698_);
                        return v___x_3704_;
                    }
                }
            } else {
                let mut v___x_3705_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v_x_3686_, 3);
                crate::leanh::lean_dec_ref(v_x_3687_);
                v___x_3705_ = 0;
                return v___x_3705_;
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq___boxed(
    mut v_x_3706_: *mut crate::leanh::LeanObject,
    mut v_x_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3708_: u8 = 0;
    let mut v_r_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_3706_, v_x_3707_);
    v_r_3709_ = crate::leanh::lean_box((v_res_3708_) as usize);
    return v_r_3709_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(
    mut v_x_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_declName_3713_ = crate::leanh::lean_ctor_get(v_x_3712_, 0);
    crate::leanh::lean_inc(v_declName_3713_);
    return v_declName_3713_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key___boxed(
    mut v_x_3714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3715_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_3714_);
    crate::leanh::lean_dec_ref(v_x_3714_);
    return v_res_3715_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(
    mut v_x_3716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3716_) {
                0 => {
                    v_declName_3717_ = crate::leanh::lean_ctor_get(v_x_3716_, 0);
                    crate::leanh::lean_inc(v_declName_3717_);
                    crate::leanh::lean_dec_ref_known(v_x_3716_, 1);
                    v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3718_, 0, v_declName_3717_);
                    v___x_3719_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3718_);
                    return v___x_3719_;
                }
                1 => {
                    v_fvarId_3720_ = crate::leanh::lean_ctor_get(v_x_3716_, 0);
                    v_isSharedCheck_3728_ = (!crate::leanh::lean_is_exclusive(v_x_3716_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3722_ = v_x_3716_;
                        v_isShared_3723_ = v_isSharedCheck_3728_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_3720_);
                        crate::leanh::lean_dec(v_x_3716_);
                        v___x_3722_ = crate::leanh::lean_box(0);
                        v_isShared_3723_ = v_isSharedCheck_3728_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_3716_);
                    v___x_3729_ = crate::leanh::lean_box(0);
                    return v___x_3729_;
                }
            },
            1 => {
                if v_isShared_3723_ == 0 {
                    v___x_3725_ = v___x_3722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_fvarId_3720_);
                    v___x_3725_ = v_reuseFailAlloc_3727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3726_, 0, v___x_3725_);
                return v___x_3726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3730_) == 0 {
                    v___x_3732_ = l_List_reverse___redArg(v_a_3731_);
                    return v___x_3732_;
                } else {
                    v_head_3733_ = crate::leanh::lean_ctor_get(v_a_3730_, 0);
                    v_tail_3734_ = crate::leanh::lean_ctor_get(v_a_3730_, 1);
                    v_isSharedCheck_3743_ = (!crate::leanh::lean_is_exclusive(v_a_3730_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3736_ = v_a_3730_;
                        v_isShared_3737_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3734_);
                        crate::leanh::lean_inc(v_head_3733_);
                        crate::leanh::lean_dec(v_a_3730_);
                        v___x_3736_ = crate::leanh::lean_box(0);
                        v_isShared_3737_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3738_ = l_Lean_mkLevelParam(v_head_3733_);
                if v_isShared_3737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3736_, 1, v_a_3731_);
                    crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3738_);
                    v___x_3740_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_a_3731_);
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
    mut v_msgData_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = lean_st_ref_get(v___y_3748_);
    v_env_3751_ = crate::leanh::lean_ctor_get(v___x_3750_, 0);
    crate::leanh::lean_inc_ref(v_env_3751_);
    crate::leanh::lean_dec(v___x_3750_);
    v___x_3752_ = lean_st_ref_get(v___y_3746_);
    v_mctx_3753_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3753_);
    crate::leanh::lean_dec(v___x_3752_);
    v_lctx_3754_ = crate::leanh::lean_ctor_get(v___y_3745_, 2);
    v_options_3755_ = crate::leanh::lean_ctor_get(v___y_3747_, 2);
    crate::leanh::lean_inc_ref(v_options_3755_);
    crate::leanh::lean_inc_ref(v_lctx_3754_);
    v___x_3756_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3756_, 0, v_env_3751_);
    crate::leanh::lean_ctor_set(v___x_3756_, 1, v_mctx_3753_);
    crate::leanh::lean_ctor_set(v___x_3756_, 2, v_lctx_3754_);
    crate::leanh::lean_ctor_set(v___x_3756_, 3, v_options_3755_);
    v___x_3757_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3757_, 0, v___x_3756_);
    crate::leanh::lean_ctor_set(v___x_3757_, 1, v_msgData_3744_);
    v___x_3758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3758_, 0, v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msgData_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
    crate::leanh::lean_dec(v___y_3763_);
    crate::leanh::lean_dec_ref(v___y_3762_);
    crate::leanh::lean_dec(v___y_3761_);
    crate::leanh::lean_dec_ref(v___y_3760_);
    return v_res_3765_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(
    mut v_msg_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3772_ = crate::leanh::lean_ctor_get(v___y_3769_, 5);
                v___x_3773_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
                v_a_3774_ = crate::leanh::lean_ctor_get(v___x_3773_, 0);
                v_isSharedCheck_3782_ = (!crate::leanh::lean_is_exclusive(v___x_3773_)) as u8;
                if v_isSharedCheck_3782_ == 0 {
                    v___x_3776_ = v___x_3773_;
                    v_isShared_3777_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3774_);
                    crate::leanh::lean_dec(v___x_3773_);
                    v___x_3776_ = crate::leanh::lean_box(0);
                    v_isShared_3777_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3772_);
                v___x_3778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3778_, 0, v_ref_3772_);
                crate::leanh::lean_ctor_set(v___x_3778_, 1, v_a_3774_);
                if v_isShared_3777_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3776_, 1);
                    crate::leanh::lean_ctor_set(v___x_3776_, 0, v___x_3778_);
                    v___x_3780_ = v___x_3776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
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
    mut v_msg_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
    mut v___y_3786_: *mut crate::leanh::LeanObject,
    mut v___y_3787_: *mut crate::leanh::LeanObject,
    mut v___y_3788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
    crate::leanh::lean_dec(v___y_3787_);
    crate::leanh::lean_dec_ref(v___y_3786_);
    crate::leanh::lean_dec(v___y_3785_);
    crate::leanh::lean_dec_ref(v___y_3784_);
    return v_res_3789_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_ref_3790_: *mut crate::leanh::LeanObject,
    mut v_msg_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3809_: u8 = 0;
    let mut v_cancelTk_x3f_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3811_: u8 = 0;
    let mut v_inheritedTraceOptions_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3797_ = crate::leanh::lean_ctor_get(v___y_3794_, 0);
    v_fileMap_3798_ = crate::leanh::lean_ctor_get(v___y_3794_, 1);
    v_options_3799_ = crate::leanh::lean_ctor_get(v___y_3794_, 2);
    v_currRecDepth_3800_ = crate::leanh::lean_ctor_get(v___y_3794_, 3);
    v_maxRecDepth_3801_ = crate::leanh::lean_ctor_get(v___y_3794_, 4);
    v_ref_3802_ = crate::leanh::lean_ctor_get(v___y_3794_, 5);
    v_currNamespace_3803_ = crate::leanh::lean_ctor_get(v___y_3794_, 6);
    v_openDecls_3804_ = crate::leanh::lean_ctor_get(v___y_3794_, 7);
    v_initHeartbeats_3805_ = crate::leanh::lean_ctor_get(v___y_3794_, 8);
    v_maxHeartbeats_3806_ = crate::leanh::lean_ctor_get(v___y_3794_, 9);
    v_quotContext_3807_ = crate::leanh::lean_ctor_get(v___y_3794_, 10);
    v_currMacroScope_3808_ = crate::leanh::lean_ctor_get(v___y_3794_, 11);
    v_diag_3809_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3794_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3810_ = crate::leanh::lean_ctor_get(v___y_3794_, 12);
    v_suppressElabErrors_3811_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3794_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3812_ = crate::leanh::lean_ctor_get(v___y_3794_, 13);
    v_ref_3813_ = l_Lean_replaceRef(v_ref_3790_, v_ref_3802_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3812_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3810_);
    crate::leanh::lean_inc(v_currMacroScope_3808_);
    crate::leanh::lean_inc(v_quotContext_3807_);
    crate::leanh::lean_inc(v_maxHeartbeats_3806_);
    crate::leanh::lean_inc(v_initHeartbeats_3805_);
    crate::leanh::lean_inc(v_openDecls_3804_);
    crate::leanh::lean_inc(v_currNamespace_3803_);
    crate::leanh::lean_inc(v_maxRecDepth_3801_);
    crate::leanh::lean_inc(v_currRecDepth_3800_);
    crate::leanh::lean_inc_ref(v_options_3799_);
    crate::leanh::lean_inc_ref(v_fileMap_3798_);
    crate::leanh::lean_inc_ref(v_fileName_3797_);
    v___x_3814_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3814_, 0, v_fileName_3797_);
    crate::leanh::lean_ctor_set(v___x_3814_, 1, v_fileMap_3798_);
    crate::leanh::lean_ctor_set(v___x_3814_, 2, v_options_3799_);
    crate::leanh::lean_ctor_set(v___x_3814_, 3, v_currRecDepth_3800_);
    crate::leanh::lean_ctor_set(v___x_3814_, 4, v_maxRecDepth_3801_);
    crate::leanh::lean_ctor_set(v___x_3814_, 5, v_ref_3813_);
    crate::leanh::lean_ctor_set(v___x_3814_, 6, v_currNamespace_3803_);
    crate::leanh::lean_ctor_set(v___x_3814_, 7, v_openDecls_3804_);
    crate::leanh::lean_ctor_set(v___x_3814_, 8, v_initHeartbeats_3805_);
    crate::leanh::lean_ctor_set(v___x_3814_, 9, v_maxHeartbeats_3806_);
    crate::leanh::lean_ctor_set(v___x_3814_, 10, v_quotContext_3807_);
    crate::leanh::lean_ctor_set(v___x_3814_, 11, v_currMacroScope_3808_);
    crate::leanh::lean_ctor_set(v___x_3814_, 12, v_cancelTk_x3f_3810_);
    crate::leanh::lean_ctor_set(v___x_3814_, 13, v_inheritedTraceOptions_3812_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3814_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3809_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3814_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3811_,
    );
    v___x_3815_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_3791_, v___y_3792_, v___y_3793_, v___x_3814_, v___y_3795_);
    crate::leanh::lean_dec_ref_known(v___x_3814_, 14);
    return v___x_3815_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_ref_3816_: *mut crate::leanh::LeanObject,
    mut v_msg_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3816_, v_msg_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
    crate::leanh::lean_dec(v___y_3821_);
    crate::leanh::lean_dec_ref(v___y_3820_);
    crate::leanh::lean_dec(v___y_3819_);
    crate::leanh::lean_dec_ref(v___y_3818_);
    crate::leanh::lean_dec(v_ref_3816_);
    return v_res_3823_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3824_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_3826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3826_, 0, v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3828_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3829_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3828_);
    crate::leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
    crate::leanh::lean_ctor_set(v___x_3829_, 2, v___x_3828_);
    crate::leanh::lean_ctor_set(v___x_3829_, 3, v___x_3828_);
    crate::leanh::lean_ctor_set(v___x_3829_, 4, v___x_3827_);
    crate::leanh::lean_ctor_set(v___x_3829_, 5, v___x_3827_);
    crate::leanh::lean_ctor_set(v___x_3829_, 6, v___x_3827_);
    crate::leanh::lean_ctor_set(v___x_3829_, 7, v___x_3827_);
    crate::leanh::lean_ctor_set(v___x_3829_, 8, v___x_3827_);
    crate::leanh::lean_ctor_set(v___x_3829_, 9, v___x_3827_);
    return v___x_3829_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3831_ = lean_mk_empty_array_with_capacity(v___x_3830_);
    v___x_3832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3832_, 0, v___x_3831_);
    return v___x_3832_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3833_: usize = 0;
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = 5usize;
    v___x_3834_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3835_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3836_ = lean_mk_empty_array_with_capacity(v___x_3835_);
    v___x_3837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_3838_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3837_);
    crate::leanh::lean_ctor_set(v___x_3838_, 1, v___x_3836_);
    crate::leanh::lean_ctor_set(v___x_3838_, 2, v___x_3834_);
    crate::leanh::lean_ctor_set(v___x_3838_, 3, v___x_3834_);
    crate::leanh::lean_ctor_set_usize(v___x_3838_, 4, v___x_3833_);
    return v___x_3838_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = crate::leanh::lean_box(1);
    v___x_3840_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_3841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3842_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3841_);
    crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3840_);
    crate::leanh::lean_ctor_set(v___x_3842_, 2, v___x_3839_);
    return v___x_3842_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_3845_ = l_Lean_stringToMessageData(v___x_3844_);
    return v___x_3845_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_3848_ = l_Lean_stringToMessageData(v___x_3847_);
    return v___x_3848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_3851_ = l_Lean_stringToMessageData(v___x_3850_);
    return v___x_3851_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_3854_ = l_Lean_stringToMessageData(v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_3857_ = l_Lean_stringToMessageData(v___x_3856_);
    return v___x_3857_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_3860_ = l_Lean_stringToMessageData(v___x_3859_);
    return v___x_3860_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3862_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_3863_ = l_Lean_stringToMessageData(v___x_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_msg_3864_: *mut crate::leanh::LeanObject,
    mut v_declHint_3865_: *mut crate::leanh::LeanObject,
    mut v___y_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    let mut v_isExporting_3871_: u8 = 0;
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3868_ = lean_st_ref_get(v___y_3866_);
                v_env_3869_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                crate::leanh::lean_inc_ref(v_env_3869_);
                crate::leanh::lean_dec(v___x_3868_);
                v___x_3870_ = l_Lean_Name_isAnonymous(v_declHint_3865_);
                if v___x_3870_ == 0 {
                    v_isExporting_3871_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3869_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3871_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3869_);
                        crate::leanh::lean_dec(v_declHint_3865_);
                        v___x_3872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3872_, 0, v_msg_3864_);
                        return v___x_3872_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3869_);
                        v___x_3873_ = l_Lean_Environment_setExporting(v_env_3869_, v___x_3870_);
                        crate::leanh::lean_inc(v_declHint_3865_);
                        crate::leanh::lean_inc_ref(v___x_3873_);
                        v___x_3874_ = l_Lean_Environment_contains(
                            v___x_3873_,
                            v_declHint_3865_,
                            v_isExporting_3871_,
                        );
                        if v___x_3874_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3873_);
                            crate::leanh::lean_dec_ref(v_env_3869_);
                            crate::leanh::lean_dec(v_declHint_3865_);
                            v___x_3875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3875_, 0, v_msg_3864_);
                            return v___x_3875_;
                        } else {
                            v___x_3876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_3877_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_3878_ = l_Lean_Options_empty;
                            v___x_3879_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3879_, 0, v___x_3873_);
                            crate::leanh::lean_ctor_set(v___x_3879_, 1, v___x_3876_);
                            crate::leanh::lean_ctor_set(v___x_3879_, 2, v___x_3877_);
                            crate::leanh::lean_ctor_set(v___x_3879_, 3, v___x_3878_);
                            crate::leanh::lean_inc(v_declHint_3865_);
                            v___x_3880_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3865_, v___x_3870_);
                            v_c_3881_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3881_, 0, v___x_3879_);
                            crate::leanh::lean_ctor_set(v_c_3881_, 1, v___x_3880_);
                            v___x_3882_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3869_,
                                v_declHint_3865_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3882_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3869_);
                                crate::leanh::lean_dec(v_declHint_3865_);
                                v___x_3883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_3884_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3884_, 0, v___x_3883_);
                                crate::leanh::lean_ctor_set(v___x_3884_, 1, v_c_3881_);
                                v___x_3885_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_3886_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3886_, 0, v___x_3884_);
                                crate::leanh::lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                                v___x_3887_ = l_Lean_MessageData_note(v___x_3886_);
                                v___x_3888_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3888_, 0, v_msg_3864_);
                                crate::leanh::lean_ctor_set(v___x_3888_, 1, v___x_3887_);
                                v___x_3889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3889_, 0, v___x_3888_);
                                return v___x_3889_;
                            } else {
                                v_val_3890_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                                v_isSharedCheck_3925_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3882_)) as u8;
                                if v_isSharedCheck_3925_ == 0 {
                                    v___x_3892_ = v___x_3882_;
                                    v_isShared_3893_ = v_isSharedCheck_3925_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3890_);
                                    crate::leanh::lean_dec(v___x_3882_);
                                    v___x_3892_ = crate::leanh::lean_box(0);
                                    v_isShared_3893_ = v_isSharedCheck_3925_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3869_);
                    crate::leanh::lean_dec(v_declHint_3865_);
                    v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3926_, 0, v_msg_3864_);
                    return v___x_3926_;
                }
            }
            1 => {
                v___x_3894_ = crate::leanh::lean_box(0);
                v___x_3895_ = l_Lean_Environment_header(v_env_3869_);
                crate::leanh::lean_dec_ref(v_env_3869_);
                v___x_3896_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3895_);
                v_mod_3897_ = lean_array_get(v___x_3894_, v___x_3896_, v_val_3890_);
                crate::leanh::lean_dec(v_val_3890_);
                crate::leanh::lean_dec_ref(v___x_3896_);
                v___x_3898_ = l_Lean_isPrivateName(v_declHint_3865_);
                crate::leanh::lean_dec(v_declHint_3865_);
                if v___x_3898_ == 0 {
                    v___x_3899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_3900_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                    crate::leanh::lean_ctor_set(v___x_3900_, 1, v_c_3881_);
                    v___x_3901_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_3902_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3902_, 0, v___x_3900_);
                    crate::leanh::lean_ctor_set(v___x_3902_, 1, v___x_3901_);
                    v___x_3903_ = l_Lean_MessageData_ofName(v_mod_3897_);
                    v___x_3904_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3904_, 0, v___x_3902_);
                    crate::leanh::lean_ctor_set(v___x_3904_, 1, v___x_3903_);
                    v___x_3905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_3906_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3906_, 0, v___x_3904_);
                    crate::leanh::lean_ctor_set(v___x_3906_, 1, v___x_3905_);
                    v___x_3907_ = l_Lean_MessageData_note(v___x_3906_);
                    v___x_3908_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3908_, 0, v_msg_3864_);
                    crate::leanh::lean_ctor_set(v___x_3908_, 1, v___x_3907_);
                    if v_isShared_3893_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3892_, 0);
                        crate::leanh::lean_ctor_set(v___x_3892_, 0, v___x_3908_);
                        v___x_3910_ = v___x_3892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
                        v___x_3910_ = v_reuseFailAlloc_3911_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_3913_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3913_, 0, v___x_3912_);
                    crate::leanh::lean_ctor_set(v___x_3913_, 1, v_c_3881_);
                    v___x_3914_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_3915_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3915_, 0, v___x_3913_);
                    crate::leanh::lean_ctor_set(v___x_3915_, 1, v___x_3914_);
                    v___x_3916_ = l_Lean_MessageData_ofName(v_mod_3897_);
                    v___x_3917_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3917_, 0, v___x_3915_);
                    crate::leanh::lean_ctor_set(v___x_3917_, 1, v___x_3916_);
                    v___x_3918_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_3919_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3917_);
                    crate::leanh::lean_ctor_set(v___x_3919_, 1, v___x_3918_);
                    v___x_3920_ = l_Lean_MessageData_note(v___x_3919_);
                    v___x_3921_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3921_, 0, v_msg_3864_);
                    crate::leanh::lean_ctor_set(v___x_3921_, 1, v___x_3920_);
                    if v_isShared_3893_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3892_, 0);
                        crate::leanh::lean_ctor_set(v___x_3892_, 0, v___x_3921_);
                        v___x_3923_ = v___x_3892_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
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
    mut v_msg_3927_: *mut crate::leanh::LeanObject,
    mut v_declHint_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3927_, v_declHint_3928_, v___y_3929_);
    crate::leanh::lean_dec(v___y_3929_);
    return v_res_3931_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(
    mut v_msg_3932_: *mut crate::leanh::LeanObject,
    mut v_declHint_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3932_, v_declHint_3933_, v___y_3937_);
                v_a_3940_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                v_isSharedCheck_3949_ = (!crate::leanh::lean_is_exclusive(v___x_3939_)) as u8;
                if v_isSharedCheck_3949_ == 0 {
                    v___x_3942_ = v___x_3939_;
                    v_isShared_3943_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3940_);
                    crate::leanh::lean_dec(v___x_3939_);
                    v___x_3942_ = crate::leanh::lean_box(0);
                    v_isShared_3943_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3944_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3945_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3945_, 0, v___x_3944_);
                crate::leanh::lean_ctor_set(v___x_3945_, 1, v_a_3940_);
                if v_isShared_3943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3942_, 0, v___x_3945_);
                    v___x_3947_ = v___x_3942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
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
    mut v_msg_3950_: *mut crate::leanh::LeanObject,
    mut v_declHint_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3950_, v_declHint_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    return v_res_3957_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_3958_: *mut crate::leanh::LeanObject,
    mut v_msg_3959_: *mut crate::leanh::LeanObject,
    mut v_declHint_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3959_, v_declHint_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
    v_a_3967_ = crate::leanh::lean_ctor_get(v___x_3966_, 0);
    crate::leanh::lean_inc(v_a_3967_);
    crate::leanh::lean_dec_ref(v___x_3966_);
    v___x_3968_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3958_, v_a_3967_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
    return v___x_3968_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_3969_: *mut crate::leanh::LeanObject,
    mut v_msg_3970_: *mut crate::leanh::LeanObject,
    mut v_declHint_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3969_, v_msg_3970_, v_declHint_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
    crate::leanh::lean_dec(v___y_3975_);
    crate::leanh::lean_dec_ref(v___y_3974_);
    crate::leanh::lean_dec(v___y_3973_);
    crate::leanh::lean_dec_ref(v___y_3972_);
    crate::leanh::lean_dec(v_ref_3969_);
    return v_res_3977_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3979_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3980_ = l_Lean_stringToMessageData(v___x_3979_);
    return v___x_3980_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3982_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3983_ = l_Lean_stringToMessageData(v___x_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3984_: *mut crate::leanh::LeanObject,
    mut v_constName_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
    mut v___y_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3991_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3992_ = 0;
    crate::leanh::lean_inc(v_constName_3985_);
    v___x_3993_ = l_Lean_MessageData_ofConstName(v_constName_3985_, v___x_3992_);
    v___x_3994_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3994_, 0, v___x_3991_);
    crate::leanh::lean_ctor_set(v___x_3994_, 1, v___x_3993_);
    v___x_3995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3996_, 0, v___x_3994_);
    crate::leanh::lean_ctor_set(v___x_3996_, 1, v___x_3995_);
    v___x_3997_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3984_, v___x_3996_, v_constName_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
    return v___x_3997_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3998_: *mut crate::leanh::LeanObject,
    mut v_constName_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_3998_, v_constName_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
    crate::leanh::lean_dec(v___y_4003_);
    crate::leanh::lean_dec_ref(v___y_4002_);
    crate::leanh::lean_dec(v___y_4001_);
    crate::leanh::lean_dec_ref(v___y_4000_);
    crate::leanh::lean_dec(v_ref_3998_);
    return v_res_4005_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(
    mut v_constName_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4012_ = crate::leanh::lean_ctor_get(v___y_4009_, 5);
    v___x_4013_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_4012_, v_constName_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
    return v___x_4013_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg___boxed(
    mut v_constName_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4020_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
    crate::leanh::lean_dec(v___y_4018_);
    crate::leanh::lean_dec_ref(v___y_4017_);
    crate::leanh::lean_dec(v___y_4016_);
    crate::leanh::lean_dec_ref(v___y_4015_);
    return v_res_4020_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(
    mut v_constName_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4027_ = lean_st_ref_get(v___y_4025_);
                v_env_4028_ = crate::leanh::lean_ctor_get(v___x_4027_, 0);
                crate::leanh::lean_inc_ref(v_env_4028_);
                crate::leanh::lean_dec(v___x_4027_);
                v___x_4029_ = 0;
                crate::leanh::lean_inc(v_constName_4021_);
                v___x_4030_ =
                    l_Lean_Environment_find_x3f(v_env_4028_, v_constName_4021_, v___x_4029_);
                if crate::leanh::lean_obj_tag(v___x_4030_) == 0 {
                    v___x_4031_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
                    return v___x_4031_;
                } else {
                    crate::leanh::lean_dec(v_constName_4021_);
                    v_val_4032_ = crate::leanh::lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4039_ = (!crate::leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4039_ == 0 {
                        v___x_4034_ = v___x_4030_;
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4032_);
                        crate::leanh::lean_dec(v___x_4030_);
                        v___x_4034_ = crate::leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4035_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4034_, 0);
                    v___x_4037_ = v___x_4034_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_val_4032_);
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
    mut v_constName_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ =
        l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(
            v_constName_4040_,
            v___y_4041_,
            v___y_4042_,
            v___y_4043_,
            v___y_4044_,
        );
    crate::leanh::lean_dec(v___y_4044_);
    crate::leanh::lean_dec_ref(v___y_4043_);
    crate::leanh::lean_dec(v___y_4042_);
    crate::leanh::lean_dec_ref(v___y_4041_);
    return v_res_4046_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(
    mut v_x_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
    mut v_a_4049_: *mut crate::leanh::LeanObject,
    mut v_a_4050_: *mut crate::leanh::LeanObject,
    mut v_a_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4058_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_a_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_fvarId_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_proof_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4047_) {
                0 => {
                    v_declName_4053_ = crate::leanh::lean_ctor_get(v_x_4047_, 0);
                    crate::leanh::lean_inc_n(v_declName_4053_, 2);
                    crate::leanh::lean_dec_ref_known(v_x_4047_, 1);
                    v___x_4054_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_4053_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
                    if crate::leanh::lean_obj_tag(v___x_4054_) == 0 {
                        v_a_4055_ = crate::leanh::lean_ctor_get(v___x_4054_, 0);
                        v_isSharedCheck_4067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4054_)) as u8;
                        if v_isSharedCheck_4067_ == 0 {
                            v___x_4057_ = v___x_4054_;
                            v_isShared_4058_ = v_isSharedCheck_4067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4055_);
                            crate::leanh::lean_dec(v___x_4054_);
                            v___x_4057_ = crate::leanh::lean_box(0);
                            v_isShared_4058_ = v_isSharedCheck_4067_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_4053_);
                        v_a_4068_ = crate::leanh::lean_ctor_get(v___x_4054_, 0);
                        v_isSharedCheck_4075_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4054_)) as u8;
                        if v_isSharedCheck_4075_ == 0 {
                            v___x_4070_ = v___x_4054_;
                            v_isShared_4071_ = v_isSharedCheck_4075_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4068_);
                            crate::leanh::lean_dec(v___x_4054_);
                            v___x_4070_ = crate::leanh::lean_box(0);
                            v_isShared_4071_ = v_isSharedCheck_4075_;
                            state = 3;
                            continue;
                        }
                    }
                }
                1 => {
                    v_fvarId_4076_ = crate::leanh::lean_ctor_get(v_x_4047_, 0);
                    v_isSharedCheck_4086_ = (!crate::leanh::lean_is_exclusive(v_x_4047_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v___x_4078_ = v_x_4047_;
                        v_isShared_4079_ = v_isSharedCheck_4086_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4076_);
                        crate::leanh::lean_dec(v_x_4047_);
                        v___x_4078_ = crate::leanh::lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4086_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_proof_4087_ = crate::leanh::lean_ctor_get(v_x_4047_, 2);
                    crate::leanh::lean_inc_ref(v_proof_4087_);
                    crate::leanh::lean_dec_ref_known(v_x_4047_, 3);
                    v___x_4088_ = crate::leanh::lean_box(0);
                    v___x_4089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4089_, 0, v___x_4088_);
                    crate::leanh::lean_ctor_set(v___x_4089_, 1, v_proof_4087_);
                    v___x_4090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4090_, 0, v___x_4089_);
                    return v___x_4090_;
                }
            },
            1 => {
                v___x_4059_ = l_Lean_ConstantInfo_levelParams(v_a_4055_);
                crate::leanh::lean_dec(v_a_4055_);
                v___x_4060_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_4059_);
                v___x_4061_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_4059_, v___x_4060_);
                v___x_4062_ = l_Lean_mkConst(v_declName_4053_, v___x_4061_);
                v___x_4063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4059_);
                crate::leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                if v_isShared_4058_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4057_, 0, v___x_4063_);
                    v___x_4065_ = v___x_4057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
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
                    v_reuseFailAlloc_4074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
                    v___x_4073_ = v_reuseFailAlloc_4074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4073_;
            }
            5 => {
                v___x_4080_ = crate::leanh::lean_box(0);
                v___x_4081_ = l_Lean_mkFVar(v_fvarId_4076_);
                v___x_4082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4080_);
                crate::leanh::lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                if v_isShared_4079_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4078_, 0);
                    crate::leanh::lean_ctor_set(v___x_4078_, 0, v___x_4082_);
                    v___x_4084_ = v___x_4078_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
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
    mut v_x_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
    mut v_a_4093_: *mut crate::leanh::LeanObject,
    mut v_a_4094_: *mut crate::leanh::LeanObject,
    mut v_a_4095_: *mut crate::leanh::LeanObject,
    mut v_a_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(
        v_x_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_,
    );
    crate::leanh::lean_dec(v_a_4095_);
    crate::leanh::lean_dec_ref(v_a_4094_);
    crate::leanh::lean_dec(v_a_4093_);
    crate::leanh::lean_dec_ref(v_a_4092_);
    return v_res_4097_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(
    mut v_00_u03b1_4098_: *mut crate::leanh::LeanObject,
    mut v_constName_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
    return v___x_4105_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___boxed(
    mut v_00_u03b1_4106_: *mut crate::leanh::LeanObject,
    mut v_constName_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4113_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0(v_00_u03b1_4106_, v_constName_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
    crate::leanh::lean_dec(v___y_4111_);
    crate::leanh::lean_dec_ref(v___y_4110_);
    crate::leanh::lean_dec(v___y_4109_);
    crate::leanh::lean_dec_ref(v___y_4108_);
    return v_res_4113_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4114_: *mut crate::leanh::LeanObject,
    mut v_ref_4115_: *mut crate::leanh::LeanObject,
    mut v_constName_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___redArg(v_ref_4115_, v_constName_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4123_: *mut crate::leanh::LeanObject,
    mut v_ref_4124_: *mut crate::leanh::LeanObject,
    mut v_constName_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4131_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1(v_00_u03b1_4123_, v_ref_4124_, v_constName_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
    crate::leanh::lean_dec(v___y_4129_);
    crate::leanh::lean_dec_ref(v___y_4128_);
    crate::leanh::lean_dec(v___y_4127_);
    crate::leanh::lean_dec_ref(v___y_4126_);
    crate::leanh::lean_dec(v_ref_4124_);
    return v_res_4131_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_4132_: *mut crate::leanh::LeanObject,
    mut v_ref_4133_: *mut crate::leanh::LeanObject,
    mut v_msg_4134_: *mut crate::leanh::LeanObject,
    mut v_declHint_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4141_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4133_, v_msg_4134_, v_declHint_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
    return v___x_4141_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_4142_: *mut crate::leanh::LeanObject,
    mut v_ref_4143_: *mut crate::leanh::LeanObject,
    mut v_msg_4144_: *mut crate::leanh::LeanObject,
    mut v_declHint_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4151_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4142_, v_ref_4143_, v_msg_4144_, v_declHint_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
    crate::leanh::lean_dec(v___y_4149_);
    crate::leanh::lean_dec_ref(v___y_4148_);
    crate::leanh::lean_dec(v___y_4147_);
    crate::leanh::lean_dec_ref(v___y_4146_);
    crate::leanh::lean_dec(v_ref_4143_);
    return v_res_4151_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(
    mut v_msg_4152_: *mut crate::leanh::LeanObject,
    mut v_declHint_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4152_, v_declHint_4153_, v___y_4157_);
    return v___x_4159_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(
    mut v_msg_4160_: *mut crate::leanh::LeanObject,
    mut v_declHint_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
    mut v___y_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4167_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_4160_, v_declHint_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
    crate::leanh::lean_dec(v___y_4165_);
    crate::leanh::lean_dec_ref(v___y_4164_);
    crate::leanh::lean_dec(v___y_4163_);
    crate::leanh::lean_dec_ref(v___y_4162_);
    return v_res_4167_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b1_4168_: *mut crate::leanh::LeanObject,
    mut v_ref_4169_: *mut crate::leanh::LeanObject,
    mut v_msg_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4169_, v_msg_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
    return v___x_4176_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b1_4177_: *mut crate::leanh::LeanObject,
    mut v_ref_4178_: *mut crate::leanh::LeanObject,
    mut v_msg_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4177_, v_ref_4178_, v_msg_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
    crate::leanh::lean_dec(v___y_4183_);
    crate::leanh::lean_dec_ref(v___y_4182_);
    crate::leanh::lean_dec(v___y_4181_);
    crate::leanh::lean_dec_ref(v___y_4180_);
    crate::leanh::lean_dec(v_ref_4178_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(
    mut v_00_u03b1_4186_: *mut crate::leanh::LeanObject,
    mut v_msg_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_msg_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_4194_: *mut crate::leanh::LeanObject,
    mut v_msg_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4201_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_4194_, v_msg_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
    crate::leanh::lean_dec(v___y_4199_);
    crate::leanh::lean_dec_ref(v___y_4198_);
    crate::leanh::lean_dec(v___y_4197_);
    crate::leanh::lean_dec_ref(v___y_4196_);
    return v_res_4201_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0()
-> u64 {
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u64 = 0;
    v___x_4202_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4203_ = lean_uint64_of_nat(v___x_4202_);
    return v___x_4203_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(
    mut v_sp_4204_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___y_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: u64 = 0;
    let mut v_hash_4208_: u64 = 0;
    let mut v_declName_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_4209_ = crate::leanh::lean_ctor_get(v_sp_4204_, 0);
                v___y_4206_ = v_declName_4209_;
                state = 1;
                continue;
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4206_) == 0 {
                    v___x_4207_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    return v___x_4207_;
                } else {
                    v_hash_4208_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_4206_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    return v_hash_4208_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___boxed(
    mut v_sp_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4211_: u64 = 0;
    let mut v_r_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0(v_sp_4210_);
    crate::leanh::lean_dec_ref(v_sp_4210_);
    v_r_4212_ = crate::leanh::lean_box_uint64(v_res_4211_);
    return v_r_4212_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(
    mut v_e_4215_: *mut crate::leanh::LeanObject,
    mut v___y_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4218_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_unused_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4218_ = l_Lean_Expr_hasMVar(v_e_4215_);
                if v___x_4218_ == 0 {
                    v___x_4219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4219_, 0, v_e_4215_);
                    return v___x_4219_;
                } else {
                    v___x_4220_ = lean_st_ref_get(v___y_4216_);
                    v_mctx_4221_ = crate::leanh::lean_ctor_get(v___x_4220_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4221_);
                    crate::leanh::lean_dec(v___x_4220_);
                    v___x_4222_ = l_Lean_instantiateMVarsCore(v_mctx_4221_, v_e_4215_);
                    v_fst_4223_ = crate::leanh::lean_ctor_get(v___x_4222_, 0);
                    crate::leanh::lean_inc(v_fst_4223_);
                    v_snd_4224_ = crate::leanh::lean_ctor_get(v___x_4222_, 1);
                    crate::leanh::lean_inc(v_snd_4224_);
                    crate::leanh::lean_dec_ref(v___x_4222_);
                    v___x_4225_ = lean_st_ref_take(v___y_4216_);
                    v_cache_4226_ = crate::leanh::lean_ctor_get(v___x_4225_, 1);
                    v_zetaDeltaFVarIds_4227_ = crate::leanh::lean_ctor_get(v___x_4225_, 2);
                    v_postponed_4228_ = crate::leanh::lean_ctor_get(v___x_4225_, 3);
                    v_diag_4229_ = crate::leanh::lean_ctor_get(v___x_4225_, 4);
                    v_isSharedCheck_4238_ = (!crate::leanh::lean_is_exclusive(v___x_4225_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v_unused_4239_ = crate::leanh::lean_ctor_get(v___x_4225_, 0);
                        crate::leanh::lean_dec(v_unused_4239_);
                        v___x_4231_ = v___x_4225_;
                        v_isShared_4232_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4229_);
                        crate::leanh::lean_inc(v_postponed_4228_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4227_);
                        crate::leanh::lean_inc(v_cache_4226_);
                        crate::leanh::lean_dec(v___x_4225_);
                        v___x_4231_ = crate::leanh::lean_box(0);
                        v_isShared_4232_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4231_, 0, v_snd_4224_);
                    v___x_4234_ = v___x_4231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4237_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_snd_4224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_cache_4226_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4237_,
                        2,
                        v_zetaDeltaFVarIds_4227_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_postponed_4228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_diag_4229_);
                    v___x_4234_ = v_reuseFailAlloc_4237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4235_ = lean_st_ref_set(v___y_4216_, v___x_4234_);
                v___x_4236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4236_, 0, v_fst_4223_);
                return v___x_4236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg___boxed(
    mut v_e_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4243_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_4240_, v___y_4241_);
    crate::leanh::lean_dec(v___y_4241_);
    return v_res_4243_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(
    mut v_e_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_e_4244_, v___y_4246_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___boxed(
    mut v_e_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4257_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0(
            v_e_4251_,
            v___y_4252_,
            v___y_4253_,
            v___y_4254_,
            v___y_4255_,
        );
    crate::leanh::lean_dec(v___y_4255_);
    crate::leanh::lean_dec_ref(v___y_4254_);
    crate::leanh::lean_dec(v___y_4253_);
    crate::leanh::lean_dec_ref(v___y_4252_);
    return v_res_4257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(
    mut v_proof_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_prf_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v_snd_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v_fst_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4289_: u8 = 0;
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut v_a_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v_a_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v_declName_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4330_: u8 = 0;
    let mut v_fvarId_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_proof_4258_) {
                0 => {
                    v_declName_4320_ = crate::leanh::lean_ctor_get(v_proof_4258_, 0);
                    crate::leanh::lean_inc(v_declName_4320_);
                    crate::leanh::lean_dec_ref_known(v_proof_4258_, 1);
                    v___x_4321_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                        v_declName_4320_,
                        v_a_4259_,
                        v_a_4260_,
                        v_a_4261_,
                        v_a_4262_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4321_) == 0 {
                        v_a_4322_ = crate::leanh::lean_ctor_get(v___x_4321_, 0);
                        crate::leanh::lean_inc(v_a_4322_);
                        crate::leanh::lean_dec_ref_known(v___x_4321_, 1);
                        v_prf_4265_ = v_a_4322_;
                        v___y_4266_ = v_a_4259_;
                        v___y_4267_ = v_a_4260_;
                        v___y_4268_ = v_a_4261_;
                        v___y_4269_ = v_a_4262_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4323_ = crate::leanh::lean_ctor_get(v___x_4321_, 0);
                        v_isSharedCheck_4330_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4321_)) as u8;
                        if v_isSharedCheck_4330_ == 0 {
                            v___x_4325_ = v___x_4321_;
                            v_isShared_4326_ = v_isSharedCheck_4330_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4323_);
                            crate::leanh::lean_dec(v___x_4321_);
                            v___x_4325_ = crate::leanh::lean_box(0);
                            v_isShared_4326_ = v_isSharedCheck_4330_;
                            state = 12;
                            continue;
                        }
                    }
                }
                1 => {
                    v_fvarId_4331_ = crate::leanh::lean_ctor_get(v_proof_4258_, 0);
                    crate::leanh::lean_inc(v_fvarId_4331_);
                    crate::leanh::lean_dec_ref_known(v_proof_4258_, 1);
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
                    v_proof_4333_ = crate::leanh::lean_ctor_get(v_proof_4258_, 2);
                    crate::leanh::lean_inc_ref(v_proof_4333_);
                    crate::leanh::lean_dec_ref_known(v_proof_4258_, 3);
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
                crate::leanh::lean_inc(v___y_4269_);
                crate::leanh::lean_inc_ref(v___y_4268_);
                crate::leanh::lean_inc(v___y_4267_);
                crate::leanh::lean_inc_ref(v___y_4266_);
                crate::leanh::lean_inc_ref(v_prf_4265_);
                v___x_4270_ = lean_infer_type(
                    v_prf_4265_,
                    v___y_4266_,
                    v___y_4267_,
                    v___y_4268_,
                    v___y_4269_,
                );
                if crate::leanh::lean_obj_tag(v___x_4270_) == 0 {
                    v_a_4271_ = crate::leanh::lean_ctor_get(v___x_4270_, 0);
                    crate::leanh::lean_inc(v_a_4271_);
                    crate::leanh::lean_dec_ref_known(v___x_4270_, 1);
                    v___x_4272_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_a_4271_, v___y_4267_);
                    v_a_4273_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    crate::leanh::lean_inc(v_a_4273_);
                    crate::leanh::lean_dec_ref(v___x_4272_);
                    v___x_4274_ = 0;
                    v___x_4275_ = l_Lean_Meta_forallMetaTelescope(
                        v_a_4273_,
                        v___x_4274_,
                        v___y_4266_,
                        v___y_4267_,
                        v___y_4268_,
                        v___y_4269_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4275_) == 0 {
                        v_a_4276_ = crate::leanh::lean_ctor_get(v___x_4275_, 0);
                        v_isSharedCheck_4303_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4275_)) as u8;
                        if v_isSharedCheck_4303_ == 0 {
                            v___x_4278_ = v___x_4275_;
                            v_isShared_4279_ = v_isSharedCheck_4303_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4276_);
                            crate::leanh::lean_dec(v___x_4275_);
                            v___x_4278_ = crate::leanh::lean_box(0);
                            v_isShared_4279_ = v_isSharedCheck_4303_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prf_4265_);
                        v_a_4304_ = crate::leanh::lean_ctor_get(v___x_4275_, 0);
                        v_isSharedCheck_4311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4275_)) as u8;
                        if v_isSharedCheck_4311_ == 0 {
                            v___x_4306_ = v___x_4275_;
                            v_isShared_4307_ = v_isSharedCheck_4311_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4304_);
                            crate::leanh::lean_dec(v___x_4275_);
                            v___x_4306_ = crate::leanh::lean_box(0);
                            v_isShared_4307_ = v_isSharedCheck_4311_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_prf_4265_);
                    v_a_4312_ = crate::leanh::lean_ctor_get(v___x_4270_, 0);
                    v_isSharedCheck_4319_ = (!crate::leanh::lean_is_exclusive(v___x_4270_)) as u8;
                    if v_isSharedCheck_4319_ == 0 {
                        v___x_4314_ = v___x_4270_;
                        v_isShared_4315_ = v_isSharedCheck_4319_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4312_);
                        crate::leanh::lean_dec(v___x_4270_);
                        v___x_4314_ = crate::leanh::lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4319_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_4280_ = crate::leanh::lean_ctor_get(v_a_4276_, 1);
                v_fst_4281_ = crate::leanh::lean_ctor_get(v_a_4276_, 0);
                v_isSharedCheck_4302_ = (!crate::leanh::lean_is_exclusive(v_a_4276_)) as u8;
                if v_isSharedCheck_4302_ == 0 {
                    v___x_4283_ = v_a_4276_;
                    v_isShared_4284_ = v_isSharedCheck_4302_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4280_);
                    crate::leanh::lean_inc(v_fst_4281_);
                    crate::leanh::lean_dec(v_a_4276_);
                    v___x_4283_ = crate::leanh::lean_box(0);
                    v_isShared_4284_ = v_isSharedCheck_4302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4285_ = crate::leanh::lean_ctor_get(v_snd_4280_, 0);
                v_snd_4286_ = crate::leanh::lean_ctor_get(v_snd_4280_, 1);
                v_isSharedCheck_4301_ = (!crate::leanh::lean_is_exclusive(v_snd_4280_)) as u8;
                if v_isSharedCheck_4301_ == 0 {
                    v___x_4288_ = v_snd_4280_;
                    v_isShared_4289_ = v_isSharedCheck_4301_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4286_);
                    crate::leanh::lean_inc(v_fst_4285_);
                    crate::leanh::lean_dec(v_snd_4280_);
                    v___x_4288_ = crate::leanh::lean_box(0);
                    v_isShared_4289_ = v_isSharedCheck_4301_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_fst_4281_);
                v___x_4290_ = l_Lean_Expr_beta(v_prf_4265_, v_fst_4281_);
                if v_isShared_4289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4288_, 0, v___x_4290_);
                    v___x_4292_ = v___x_4288_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 1, v_snd_4286_);
                    v___x_4292_ = v_reuseFailAlloc_4300_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4284_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4283_, 1, v___x_4292_);
                    crate::leanh::lean_ctor_set(v___x_4283_, 0, v_fst_4285_);
                    v___x_4294_ = v___x_4283_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4299_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_fst_4285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 1, v___x_4292_);
                    v___x_4294_ = v_reuseFailAlloc_4299_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4295_, 0, v_fst_4281_);
                crate::leanh::lean_ctor_set(v___x_4295_, 1, v___x_4294_);
                if v_isShared_4279_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4278_, 0, v___x_4295_);
                    v___x_4297_ = v___x_4278_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
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
                    v_reuseFailAlloc_4310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
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
                    v_reuseFailAlloc_4318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
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
                    v_reuseFailAlloc_4329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
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
    mut v_proof_4334_: *mut crate::leanh::LeanObject,
    mut v_a_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(
        v_proof_4334_,
        v_a_4335_,
        v_a_4336_,
        v_a_4337_,
        v_a_4338_,
    );
    crate::leanh::lean_dec(v_a_4338_);
    crate::leanh::lean_dec_ref(v_a_4337_);
    crate::leanh::lean_dec(v_a_4336_);
    crate::leanh::lean_dec_ref(v_a_4335_);
    return v_res_4340_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__0;
    v___x_4343_ = l_Lean_stringToMessageData(v___x_4342_);
    return v___x_4343_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__2;
    v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__4;
    v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
    return v___x_4349_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4351_ = l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__6;
    v___x_4352_ = l_Lean_stringToMessageData(v___x_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0(
    mut v_x_4353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4353_) {
        0 => {
            let mut v_declName_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_declName_4354_ = crate::leanh::lean_ctor_get(v_x_4353_, 0);
            crate::leanh::lean_inc(v_declName_4354_);
            crate::leanh::lean_dec_ref_known(v_x_4353_, 1);
            v___x_4355_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__1);
            v___x_4356_ = l_Lean_MessageData_ofName(v_declName_4354_);
            v___x_4357_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4355_);
            crate::leanh::lean_ctor_set(v___x_4357_, 1, v___x_4356_);
            return v___x_4357_;
        }
        1 => {
            let mut v_fvarId_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_4358_ = crate::leanh::lean_ctor_get(v_x_4353_, 0);
            crate::leanh::lean_inc(v_fvarId_4358_);
            crate::leanh::lean_dec_ref_known(v_x_4353_, 1);
            v___x_4359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__3);
            v___x_4360_ = l_Lean_mkFVar(v_fvarId_4358_);
            v___x_4361_ = l_Lean_MessageData_ofExpr(v___x_4360_);
            v___x_4362_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4362_, 0, v___x_4359_);
            crate::leanh::lean_ctor_set(v___x_4362_, 1, v___x_4361_);
            return v___x_4362_;
        }
        _ => {
            let mut v_ref_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_proof_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ref_4363_ = crate::leanh::lean_ctor_get(v_x_4353_, 1);
            crate::leanh::lean_inc(v_ref_4363_);
            v_proof_4364_ = crate::leanh::lean_ctor_get(v_x_4353_, 2);
            crate::leanh::lean_inc_ref(v_proof_4364_);
            crate::leanh::lean_dec_ref_known(v_x_4353_, 3);
            v___x_4365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__5);
            v___x_4366_ = l_Lean_MessageData_ofSyntax(v_ref_4363_);
            v___x_4367_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4367_, 0, v___x_4365_);
            crate::leanh::lean_ctor_set(v___x_4367_, 1, v___x_4366_);
            v___x_4368_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instToMessageDataSpecProof___lam__0___closed__7);
            v___x_4369_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4369_, 0, v___x_4367_);
            crate::leanh::lean_ctor_set(v___x_4369_, 1, v___x_4368_);
            v___x_4370_ = l_Lean_MessageData_ofExpr(v_proof_4364_);
            v___x_4371_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4371_, 0, v___x_4369_);
            crate::leanh::lean_ctor_set(v___x_4371_, 1, v___x_4370_);
            return v___x_4371_;
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4379_ = crate::leanh::lean_box(0);
    v___x_4380_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__2;
    v___x_4381_ = l_Lean_Expr_const___override(v___x_4380_, v___x_4379_);
    return v___x_4381_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4383_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4384_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default;
    v___x_4385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__3,
    );
    v___x_4386_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default___closed__0;
    v___x_4387_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4386_);
    crate::leanh::lean_ctor_set(v___x_4387_, 1, v___x_4385_);
    crate::leanh::lean_ctor_set(v___x_4387_, 2, v___x_4384_);
    crate::leanh::lean_ctor_set(v___x_4387_, 3, v___x_4383_);
    crate::leanh::lean_ctor_set(v___x_4387_, 4, v___x_4382_);
    return v___x_4387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4388_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default;
    return v___x_4389_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(
    mut v_xs_4390_: *mut crate::leanh::LeanObject,
    mut v_ys_4391_: *mut crate::leanh::LeanObject,
    mut v_x_4392_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4394_: u8 = 0;
    let mut v_one_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4393_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4394_ = lean_nat_dec_eq(v_x_4392_, v_zero_4393_);
                if v_isZero_4394_ == 1 {
                    crate::leanh::lean_dec(v_x_4392_);
                    return v_isZero_4394_;
                } else {
                    v_one_4395_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4396_ = lean_nat_sub(v_x_4392_, v_one_4395_);
                    crate::leanh::lean_dec(v_x_4392_);
                    v___x_4397_ = lean_array_fget_borrowed(v_xs_4390_, v_n_4396_);
                    v___x_4398_ = lean_array_fget_borrowed(v_ys_4391_, v_n_4396_);
                    v___x_4399_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_4397_, v___x_4398_);
                    if v___x_4399_ == 0 {
                        crate::leanh::lean_dec(v_n_4396_);
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
    mut v_xs_4401_: *mut crate::leanh::LeanObject,
    mut v_ys_4402_: *mut crate::leanh::LeanObject,
    mut v_x_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4404_: u8 = 0;
    let mut v_r_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4404_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_4401_, v_ys_4402_, v_x_4403_);
    crate::leanh::lean_dec_ref(v_ys_4402_);
    crate::leanh::lean_dec_ref(v_xs_4401_);
    v_r_4405_ = crate::leanh::lean_box((v_res_4404_) as usize);
    return v_r_4405_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(
    mut v_x_4406_: *mut crate::leanh::LeanObject,
    mut v_x_4407_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_keys_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prog_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_etaPotential_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prog_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_etaPotential_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: u8 = 0;
    v_keys_4408_ = crate::leanh::lean_ctor_get(v_x_4406_, 0);
    crate::leanh::lean_inc_ref(v_keys_4408_);
    v_prog_4409_ = crate::leanh::lean_ctor_get(v_x_4406_, 1);
    crate::leanh::lean_inc_ref(v_prog_4409_);
    v_proof_4410_ = crate::leanh::lean_ctor_get(v_x_4406_, 2);
    crate::leanh::lean_inc_ref(v_proof_4410_);
    v_etaPotential_4411_ = crate::leanh::lean_ctor_get(v_x_4406_, 3);
    crate::leanh::lean_inc(v_etaPotential_4411_);
    v_priority_4412_ = crate::leanh::lean_ctor_get(v_x_4406_, 4);
    crate::leanh::lean_inc(v_priority_4412_);
    crate::leanh::lean_dec_ref(v_x_4406_);
    v_keys_4413_ = crate::leanh::lean_ctor_get(v_x_4407_, 0);
    crate::leanh::lean_inc_ref(v_keys_4413_);
    v_prog_4414_ = crate::leanh::lean_ctor_get(v_x_4407_, 1);
    crate::leanh::lean_inc_ref(v_prog_4414_);
    v_proof_4415_ = crate::leanh::lean_ctor_get(v_x_4407_, 2);
    crate::leanh::lean_inc_ref(v_proof_4415_);
    v_etaPotential_4416_ = crate::leanh::lean_ctor_get(v_x_4407_, 3);
    crate::leanh::lean_inc(v_etaPotential_4416_);
    v_priority_4417_ = crate::leanh::lean_ctor_get(v_x_4407_, 4);
    crate::leanh::lean_inc(v_priority_4417_);
    crate::leanh::lean_dec_ref(v_x_4407_);
    v___x_4418_ = lean_array_get_size(v_keys_4408_);
    v___x_4419_ = lean_array_get_size(v_keys_4413_);
    v___x_4420_ = lean_nat_dec_eq(v___x_4418_, v___x_4419_);
    if v___x_4420_ == 0 {
        crate::leanh::lean_dec(v_priority_4417_);
        crate::leanh::lean_dec(v_etaPotential_4416_);
        crate::leanh::lean_dec_ref(v_proof_4415_);
        crate::leanh::lean_dec_ref(v_prog_4414_);
        crate::leanh::lean_dec_ref(v_keys_4413_);
        crate::leanh::lean_dec(v_priority_4412_);
        crate::leanh::lean_dec(v_etaPotential_4411_);
        crate::leanh::lean_dec_ref(v_proof_4410_);
        crate::leanh::lean_dec_ref(v_prog_4409_);
        crate::leanh::lean_dec_ref(v_keys_4408_);
        return v___x_4420_;
    } else {
        let mut v___x_4421_: u8 = 0;
        v___x_4421_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_keys_4408_, v_keys_4413_, v___x_4418_);
        crate::leanh::lean_dec_ref(v_keys_4413_);
        crate::leanh::lean_dec_ref(v_keys_4408_);
        if v___x_4421_ == 0 {
            crate::leanh::lean_dec(v_priority_4417_);
            crate::leanh::lean_dec(v_etaPotential_4416_);
            crate::leanh::lean_dec_ref(v_proof_4415_);
            crate::leanh::lean_dec_ref(v_prog_4414_);
            crate::leanh::lean_dec(v_priority_4412_);
            crate::leanh::lean_dec(v_etaPotential_4411_);
            crate::leanh::lean_dec_ref(v_proof_4410_);
            crate::leanh::lean_dec_ref(v_prog_4409_);
            return v___x_4421_;
        } else {
            let mut v___x_4422_: u8 = 0;
            v___x_4422_ = lean_expr_eqv(v_prog_4409_, v_prog_4414_);
            crate::leanh::lean_dec_ref(v_prog_4414_);
            crate::leanh::lean_dec_ref(v_prog_4409_);
            if v___x_4422_ == 0 {
                crate::leanh::lean_dec(v_priority_4417_);
                crate::leanh::lean_dec(v_etaPotential_4416_);
                crate::leanh::lean_dec_ref(v_proof_4415_);
                crate::leanh::lean_dec(v_priority_4412_);
                crate::leanh::lean_dec(v_etaPotential_4411_);
                crate::leanh::lean_dec_ref(v_proof_4410_);
                return v___x_4422_;
            } else {
                let mut v___x_4423_: u8 = 0;
                v___x_4423_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                    v_proof_4410_,
                    v_proof_4415_,
                );
                if v___x_4423_ == 0 {
                    crate::leanh::lean_dec(v_priority_4417_);
                    crate::leanh::lean_dec(v_etaPotential_4416_);
                    crate::leanh::lean_dec(v_priority_4412_);
                    crate::leanh::lean_dec(v_etaPotential_4411_);
                    return v___x_4423_;
                } else {
                    let mut v___x_4424_: u8 = 0;
                    v___x_4424_ = lean_nat_dec_eq(v_etaPotential_4411_, v_etaPotential_4416_);
                    crate::leanh::lean_dec(v_etaPotential_4416_);
                    crate::leanh::lean_dec(v_etaPotential_4411_);
                    if v___x_4424_ == 0 {
                        crate::leanh::lean_dec(v_priority_4417_);
                        crate::leanh::lean_dec(v_priority_4412_);
                        return v___x_4424_;
                    } else {
                        let mut v___x_4425_: u8 = 0;
                        v___x_4425_ = lean_nat_dec_eq(v_priority_4412_, v_priority_4417_);
                        crate::leanh::lean_dec(v_priority_4417_);
                        crate::leanh::lean_dec(v_priority_4412_);
                        return v___x_4425_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq___boxed(
    mut v_x_4426_: *mut crate::leanh::LeanObject,
    mut v_x_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4428_: u8 = 0;
    let mut v_r_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(v_x_4426_, v_x_4427_);
    v_r_4429_ = crate::leanh::lean_box((v_res_4428_) as usize);
    return v_r_4429_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(
    mut v_xs_4430_: *mut crate::leanh::LeanObject,
    mut v_ys_4431_: *mut crate::leanh::LeanObject,
    mut v_hsz_4432_: *mut crate::leanh::LeanObject,
    mut v_x_4433_: *mut crate::leanh::LeanObject,
    mut v_x_4434_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4435_: u8 = 0;
    v___x_4435_ = l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___redArg(v_xs_4430_, v_ys_4431_, v_x_4433_);
    return v___x_4435_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0___boxed(
    mut v_xs_4436_: *mut crate::leanh::LeanObject,
    mut v_ys_4437_: *mut crate::leanh::LeanObject,
    mut v_hsz_4438_: *mut crate::leanh::LeanObject,
    mut v_x_4439_: *mut crate::leanh::LeanObject,
    mut v_x_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4441_: u8 = 0;
    let mut v_r_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4441_ =
        l_Array_isEqvAux___at___00Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq_spec__0(
            v_xs_4436_,
            v_ys_4437_,
            v_hsz_4438_,
            v_x_4439_,
            v_x_4440_,
        );
    crate::leanh::lean_dec_ref(v_ys_4437_);
    crate::leanh::lean_dec_ref(v_xs_4436_);
    v_r_4442_ = crate::leanh::lean_box((v_res_4441_) as usize);
    return v_r_4442_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4445_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4445_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4446_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__0);
    v___x_4447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4447_, 0, v___x_4446_);
    return v___x_4447_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(
    mut v_00_u03b2_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0___closed__1);
    return v___x_4449_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4450_ = l_Lean_Meta_DiscrTree_empty(crate::leanh::lean_box(0));
    return v___x_4450_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default_spec__0(crate::leanh::lean_box(0));
    return v___x_4451_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__1,
    );
    v___x_4453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default___closed__0,
    );
    v___x_4454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4454_, 0, v___x_4453_);
    crate::leanh::lean_ctor_set(v___x_4454_, 1, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
    return v___x_4456_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_x_4457_: *mut crate::leanh::LeanObject,
    mut v_x_4458_: *mut crate::leanh::LeanObject,
    mut v_x_4459_: *mut crate::leanh::LeanObject,
    mut v_x_4460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4461_ = crate::leanh::lean_ctor_get(v_x_4457_, 0);
                v_vs_4462_ = crate::leanh::lean_ctor_get(v_x_4457_, 1);
                v_isSharedCheck_4486_ = (!crate::leanh::lean_is_exclusive(v_x_4457_)) as u8;
                if v_isSharedCheck_4486_ == 0 {
                    v___x_4464_ = v_x_4457_;
                    v_isShared_4465_ = v_isSharedCheck_4486_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4462_);
                    crate::leanh::lean_inc(v_ks_4461_);
                    crate::leanh::lean_dec(v_x_4457_);
                    v___x_4464_ = crate::leanh::lean_box(0);
                    v_isShared_4465_ = v_isSharedCheck_4486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4466_ = lean_array_get_size(v_ks_4461_);
                v___x_4467_ = lean_nat_dec_lt(v_x_4458_, v___x_4466_);
                if v___x_4467_ == 0 {
                    crate::leanh::lean_dec(v_x_4458_);
                    v___x_4468_ = lean_array_push(v_ks_4461_, v_x_4459_);
                    v___x_4469_ = lean_array_push(v_vs_4462_, v_x_4460_);
                    if v_isShared_4465_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4464_, 1, v___x_4469_);
                        crate::leanh::lean_ctor_set(v___x_4464_, 0, v___x_4468_);
                        v___x_4471_ = v___x_4464_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4472_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4468_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4469_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_ks_4461_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_vs_4462_);
                            v___x_4476_ = v_reuseFailAlloc_4480_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4481_ = lean_array_fset(v_ks_4461_, v_x_4458_, v_x_4459_);
                        v___x_4482_ = lean_array_fset(v_vs_4462_, v_x_4458_, v_x_4460_);
                        crate::leanh::lean_dec(v_x_4458_);
                        if v_isShared_4465_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4464_, 1, v___x_4482_);
                            crate::leanh::lean_ctor_set(v___x_4464_, 0, v___x_4481_);
                            v___x_4484_ = v___x_4464_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4485_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4481_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 1, v___x_4482_);
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
                v___x_4477_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4478_ = lean_nat_add(v_x_4458_, v___x_4477_);
                crate::leanh::lean_dec(v_x_4458_);
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
    mut v_n_4487_: *mut crate::leanh::LeanObject,
    mut v_k_4488_: *mut crate::leanh::LeanObject,
    mut v_v_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_4496_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__0);
    v___x_4497_ = lean_usize_sub(v___x_4496_, v___x_4495_);
    return v___x_4497_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4498_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(
    mut v_x_4499_: *mut crate::leanh::LeanObject,
    mut v_x_4500_: usize,
    mut v_x_4501_: usize,
    mut v_x_4502_: *mut crate::leanh::LeanObject,
    mut v_x_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: usize = 0;
    let mut v___x_4506_: usize = 0;
    let mut v___x_4507_: usize = 0;
    let mut v___x_4508_: usize = 0;
    let mut v_j_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4514_: u8 = 0;
    let mut v_v_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4529_: u8 = 0;
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_node_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v___x_4540_: usize = 0;
    let mut v___x_4541_: usize = 0;
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut v_unused_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4559_: u8 = 0;
    let mut v_ks_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: usize = 0;
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4499_) == 0 {
                    v_es_4504_ = crate::leanh::lean_ctor_get(v_x_4499_, 0);
                    v___x_4505_ = 5usize;
                    v___x_4506_ = 1usize;
                    v___x_4507_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4508_ = lean_usize_land(v_x_4500_, v___x_4507_);
                    v_j_4509_ = lean_usize_to_nat(v___x_4508_);
                    v___x_4510_ = lean_array_get_size(v_es_4504_);
                    v___x_4511_ = lean_nat_dec_lt(v_j_4509_, v___x_4510_);
                    if v___x_4511_ == 0 {
                        crate::leanh::lean_dec(v_j_4509_);
                        crate::leanh::lean_dec(v_x_4503_);
                        crate::leanh::lean_dec(v_x_4502_);
                        return v_x_4499_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4504_);
                        v_isSharedCheck_4548_ = (!crate::leanh::lean_is_exclusive(v_x_4499_)) as u8;
                        if v_isSharedCheck_4548_ == 0 {
                            v_unused_4549_ = crate::leanh::lean_ctor_get(v_x_4499_, 0);
                            crate::leanh::lean_dec(v_unused_4549_);
                            v___x_4513_ = v_x_4499_;
                            v_isShared_4514_ = v_isSharedCheck_4548_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4499_);
                            v___x_4513_ = crate::leanh::lean_box(0);
                            v_isShared_4514_ = v_isSharedCheck_4548_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4550_ = crate::leanh::lean_ctor_get(v_x_4499_, 0);
                    v_vs_4551_ = crate::leanh::lean_ctor_get(v_x_4499_, 1);
                    v_isSharedCheck_4571_ = (!crate::leanh::lean_is_exclusive(v_x_4499_)) as u8;
                    if v_isSharedCheck_4571_ == 0 {
                        v___x_4553_ = v_x_4499_;
                        v_isShared_4554_ = v_isSharedCheck_4571_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4551_);
                        crate::leanh::lean_inc(v_ks_4550_);
                        crate::leanh::lean_dec(v_x_4499_);
                        v___x_4553_ = crate::leanh::lean_box(0);
                        v_isShared_4554_ = v_isSharedCheck_4571_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4515_ = lean_array_fget(v_es_4504_, v_j_4509_);
                v___x_4516_ = crate::leanh::lean_box(0);
                v_xs_x27_4517_ = lean_array_fset(v_es_4504_, v_j_4509_, v___x_4516_);
                match crate::leanh::lean_obj_tag(v_v_4515_) {
                    0 => {
                        v_key_4524_ = crate::leanh::lean_ctor_get(v_v_4515_, 0);
                        v_val_4525_ = crate::leanh::lean_ctor_get(v_v_4515_, 1);
                        v_isSharedCheck_4535_ = (!crate::leanh::lean_is_exclusive(v_v_4515_)) as u8;
                        if v_isSharedCheck_4535_ == 0 {
                            v___x_4527_ = v_v_4515_;
                            v_isShared_4528_ = v_isSharedCheck_4535_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4525_);
                            crate::leanh::lean_inc(v_key_4524_);
                            crate::leanh::lean_dec(v_v_4515_);
                            v___x_4527_ = crate::leanh::lean_box(0);
                            v_isShared_4528_ = v_isSharedCheck_4535_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4536_ = crate::leanh::lean_ctor_get(v_v_4515_, 0);
                        v_isSharedCheck_4546_ = (!crate::leanh::lean_is_exclusive(v_v_4515_)) as u8;
                        if v_isSharedCheck_4546_ == 0 {
                            v___x_4538_ = v_v_4515_;
                            v_isShared_4539_ = v_isSharedCheck_4546_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4536_);
                            crate::leanh::lean_dec(v_v_4515_);
                            v___x_4538_ = crate::leanh::lean_box(0);
                            v_isShared_4539_ = v_isSharedCheck_4546_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4547_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4547_, 0, v_x_4502_);
                        crate::leanh::lean_ctor_set(v___x_4547_, 1, v_x_4503_);
                        v___y_4519_ = v___x_4547_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4520_ = lean_array_fset(v_xs_x27_4517_, v_j_4509_, v___y_4519_);
                crate::leanh::lean_dec(v_j_4509_);
                if v_isShared_4514_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4513_, 0, v___x_4520_);
                    v___x_4522_ = v___x_4513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
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
                    crate::leanh::lean_del_object(v___x_4527_);
                    v___x_4530_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4524_,
                        v_val_4525_,
                        v_x_4502_,
                        v_x_4503_,
                    );
                    v___x_4531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4531_, 0, v___x_4530_);
                    v___y_4519_ = v___x_4531_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4525_);
                    crate::leanh::lean_dec(v_key_4524_);
                    if v_isShared_4528_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4527_, 1, v_x_4503_);
                        crate::leanh::lean_ctor_set(v___x_4527_, 0, v_x_4502_);
                        v___x_4533_ = v___x_4527_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_x_4502_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_x_4503_);
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
                    crate::leanh::lean_ctor_set(v___x_4538_, 0, v___x_4542_);
                    v___x_4544_ = v___x_4538_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
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
                    v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_ks_4550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_vs_4551_);
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
                    v___x_4568_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4569_ = lean_nat_dec_lt(v___x_4567_, v___x_4568_);
                    crate::leanh::lean_dec(v___x_4567_);
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
                    v_ks_4560_ = crate::leanh::lean_ctor_get(v_newNode_4557_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4560_);
                    v_vs_4561_ = crate::leanh::lean_ctor_get(v_newNode_4557_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4561_);
                    crate::leanh::lean_dec_ref(v_newNode_4557_);
                    v___x_4562_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4563_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__2);
                    v___x_4564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4501_, v_ks_4560_, v_vs_4561_, v___x_4562_, v___x_4563_);
                    crate::leanh::lean_dec_ref(v_vs_4561_);
                    crate::leanh::lean_dec_ref(v_ks_4560_);
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
    mut v_keys_4573_: *mut crate::leanh::LeanObject,
    mut v_vals_4574_: *mut crate::leanh::LeanObject,
    mut v_i_4575_: *mut crate::leanh::LeanObject,
    mut v_entries_4576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v_k_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u64 = 0;
    let mut v_h_4582_: usize = 0;
    let mut v___x_4583_: usize = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: usize = 0;
    let mut v___x_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v_h_4588_: usize = 0;
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4577_ = lean_array_get_size(v_keys_4573_);
                v___x_4578_ = lean_nat_dec_lt(v_i_4575_, v___x_4577_);
                if v___x_4578_ == 0 {
                    crate::leanh::lean_dec(v_i_4575_);
                    return v_entries_4576_;
                } else {
                    v_k_4579_ = lean_array_fget_borrowed(v_keys_4573_, v_i_4575_);
                    v_v_4580_ = lean_array_fget_borrowed(v_vals_4574_, v_i_4575_);
                    v___x_4581_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_4579_);
                    v_h_4582_ = lean_uint64_to_usize(v___x_4581_);
                    v___x_4583_ = 5usize;
                    v___x_4584_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4585_ = 1usize;
                    v___x_4586_ = lean_usize_sub(v_depth_4572_, v___x_4585_);
                    v___x_4587_ = lean_usize_mul(v___x_4583_, v___x_4586_);
                    v_h_4588_ = lean_usize_shift_right(v_h_4582_, v___x_4587_);
                    v___x_4589_ = lean_nat_add(v_i_4575_, v___x_4584_);
                    crate::leanh::lean_dec(v_i_4575_);
                    crate::leanh::lean_inc(v_v_4580_);
                    crate::leanh::lean_inc(v_k_4579_);
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
    mut v_depth_4592_: *mut crate::leanh::LeanObject,
    mut v_keys_4593_: *mut crate::leanh::LeanObject,
    mut v_vals_4594_: *mut crate::leanh::LeanObject,
    mut v_i_4595_: *mut crate::leanh::LeanObject,
    mut v_entries_4596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4597_: usize = 0;
    let mut v_res_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4597_ = crate::leanh::lean_unbox_usize(v_depth_4592_);
    crate::leanh::lean_dec(v_depth_4592_);
    v_res_4598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_4597_, v_keys_4593_, v_vals_4594_, v_i_4595_, v_entries_4596_);
    crate::leanh::lean_dec_ref(v_vals_4594_);
    crate::leanh::lean_dec_ref(v_keys_4593_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_4599_: *mut crate::leanh::LeanObject,
    mut v_x_4600_: *mut crate::leanh::LeanObject,
    mut v_x_4601_: *mut crate::leanh::LeanObject,
    mut v_x_4602_: *mut crate::leanh::LeanObject,
    mut v_x_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1605__boxed_4604_: usize = 0;
    let mut v_x_1606__boxed_4605_: usize = 0;
    let mut v_res_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1605__boxed_4604_ = crate::leanh::lean_unbox_usize(v_x_4600_);
    crate::leanh::lean_dec(v_x_4600_);
    v_x_1606__boxed_4605_ = crate::leanh::lean_unbox_usize(v_x_4601_);
    crate::leanh::lean_dec(v_x_4601_);
    v_res_4606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_4599_, v_x_1605__boxed_4604_, v_x_1606__boxed_4605_, v_x_4602_, v_x_4603_);
    return v_res_4606_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(
    mut v_x_4607_: *mut crate::leanh::LeanObject,
    mut v_x_4608_: *mut crate::leanh::LeanObject,
    mut v_x_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4610_: u64 = 0;
    let mut v___x_4611_: usize = 0;
    let mut v___x_4612_: usize = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4608_);
    v___x_4611_ = lean_uint64_to_usize(v___x_4610_);
    v___x_4612_ = 1usize;
    v___x_4613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_4607_, v___x_4611_, v___x_4612_, v_x_4608_, v_x_4609_);
    return v___x_4613_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(
    mut v_vs_4614_: *mut crate::leanh::LeanObject,
    mut v_v_4615_: *mut crate::leanh::LeanObject,
    mut v_i_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4617_ = lean_array_get_size(v_vs_4614_);
                v___x_4618_ = lean_nat_dec_lt(v_i_4616_, v___x_4617_);
                if v___x_4618_ == 0 {
                    crate::leanh::lean_dec(v_i_4616_);
                    v___x_4619_ = lean_array_push(v_vs_4614_, v_v_4615_);
                    return v___x_4619_;
                } else {
                    v___x_4620_ = lean_array_fget_borrowed(v_vs_4614_, v_i_4616_);
                    crate::leanh::lean_inc(v___x_4620_);
                    crate::leanh::lean_inc_ref(v_v_4615_);
                    v___x_4621_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheorem_beq(
                        v_v_4615_,
                        v___x_4620_,
                    );
                    if v___x_4621_ == 0 {
                        v___x_4622_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4623_ = lean_nat_add(v_i_4616_, v___x_4622_);
                        crate::leanh::lean_dec(v_i_4616_);
                        v_i_4616_ = v___x_4623_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4625_ = lean_array_fset(v_vs_4614_, v_i_4616_, v_v_4615_);
                        crate::leanh::lean_dec(v_i_4616_);
                        return v___x_4625_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5(
    mut v_vs_4626_: *mut crate::leanh::LeanObject,
    mut v_v_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4629_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__5_spec__10(v_vs_4626_, v_v_4627_, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(
    mut v_a_4630_: *mut crate::leanh::LeanObject,
    mut v_b_4631_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    v_fst_4632_ = crate::leanh::lean_ctor_get(v_a_4630_, 0);
    v_fst_4633_ = crate::leanh::lean_ctor_get(v_b_4631_, 0);
    v___x_4634_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_4632_, v_fst_4633_);
    return v___x_4634_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1___boxed(
    mut v_a_4635_: *mut crate::leanh::LeanObject,
    mut v_b_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4637_: u8 = 0;
    let mut v_r_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4637_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_a_4635_, v_b_4636_);
    crate::leanh::lean_dec_ref(v_b_4636_);
    crate::leanh::lean_dec_ref(v_a_4635_);
    v_r_4638_ = crate::leanh::lean_box((v_res_4637_) as usize);
    return v_r_4638_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(
    mut v_x_4639_: *mut crate::leanh::LeanObject,
    mut v_keys_4640_: *mut crate::leanh::LeanObject,
    mut v_v_4641_: *mut crate::leanh::LeanObject,
    mut v_k_4642_: *mut crate::leanh::LeanObject,
    mut v_x_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4645_ = lean_nat_add(v_x_4639_, v___x_4644_);
    v_c_4646_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        crate::leanh::lean_box(0),
        v_keys_4640_,
        v_v_4641_,
        v___x_4645_,
    );
    crate::leanh::lean_dec(v___x_4645_);
    v___x_4647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4647_, 0, v_k_4642_);
    crate::leanh::lean_ctor_set(v___x_4647_, 1, v_c_4646_);
    return v___x_4647_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0___boxed(
    mut v_x_4648_: *mut crate::leanh::LeanObject,
    mut v_keys_4649_: *mut crate::leanh::LeanObject,
    mut v_v_4650_: *mut crate::leanh::LeanObject,
    mut v_k_4651_: *mut crate::leanh::LeanObject,
    mut v_x_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4648_, v_keys_4649_, v_v_4650_, v_k_4651_, v_x_4652_);
    crate::leanh::lean_dec_ref(v_keys_4649_);
    crate::leanh::lean_dec(v_x_4648_);
    return v_res_4653_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_x_4658_: *mut crate::leanh::LeanObject,
    mut v_keys_4659_: *mut crate::leanh::LeanObject,
    mut v_v_4660_: *mut crate::leanh::LeanObject,
    mut v_k_4661_: *mut crate::leanh::LeanObject,
    mut v_as_4662_: *mut crate::leanh::LeanObject,
    mut v_k_4663_: *mut crate::leanh::LeanObject,
    mut v_x_4664_: *mut crate::leanh::LeanObject,
    mut v_x_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: u8 = 0;
    let mut v_snd_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut v_unused_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: u8 = 0;
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4666_ = lean_nat_add(v_x_4664_, v_x_4665_);
                v___x_4667_ = crate::leanh::lean_unsigned_to_nat(1);
                v_mid_4668_ = lean_nat_shiftr(v___x_4666_, v___x_4667_);
                crate::leanh::lean_dec(v___x_4666_);
                v_midVal_4669_ = lean_array_fget(v_as_4662_, v_mid_4668_);
                v___x_4670_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_midVal_4669_, v_k_4663_);
                if v___x_4670_ == 0 {
                    crate::leanh::lean_dec(v_x_4665_);
                    v___x_4671_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__1(v_k_4663_, v_midVal_4669_);
                    if v___x_4671_ == 0 {
                        crate::leanh::lean_dec(v_x_4664_);
                        v___x_4672_ = lean_array_get_size(v_as_4662_);
                        v___x_4673_ = lean_nat_dec_lt(v_mid_4668_, v___x_4672_);
                        if v___x_4673_ == 0 {
                            crate::leanh::lean_dec(v_midVal_4669_);
                            crate::leanh::lean_dec(v_mid_4668_);
                            crate::leanh::lean_dec(v_k_4661_);
                            crate::leanh::lean_dec_ref(v_v_4660_);
                            return v_as_4662_;
                        } else {
                            v_snd_4674_ = crate::leanh::lean_ctor_get(v_midVal_4669_, 1);
                            v_isSharedCheck_4686_ =
                                (!crate::leanh::lean_is_exclusive(v_midVal_4669_)) as u8;
                            if v_isSharedCheck_4686_ == 0 {
                                v_unused_4687_ = crate::leanh::lean_ctor_get(v_midVal_4669_, 0);
                                crate::leanh::lean_dec(v_unused_4687_);
                                v___x_4676_ = v_midVal_4669_;
                                v_isShared_4677_ = v_isSharedCheck_4686_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4674_);
                                crate::leanh::lean_dec(v_midVal_4669_);
                                v___x_4676_ = crate::leanh::lean_box(0);
                                v_isShared_4677_ = v_isSharedCheck_4686_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_midVal_4669_);
                        v_x_4665_ = v_mid_4668_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_midVal_4669_);
                    v___x_4689_ = lean_nat_dec_eq(v_mid_4668_, v_x_4664_);
                    if v___x_4689_ == 0 {
                        crate::leanh::lean_dec(v_x_4664_);
                        v_x_4664_ = v_mid_4668_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mid_4668_);
                        crate::leanh::lean_dec(v_x_4665_);
                        v___x_4691_ = lean_nat_add(v_x_4658_, v___x_4667_);
                        v_c_4692_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(crate::leanh::lean_box(0), v_keys_4659_, v_v_4660_, v___x_4691_);
                        crate::leanh::lean_dec(v___x_4691_);
                        v___x_4693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4693_, 0, v_k_4661_);
                        crate::leanh::lean_ctor_set(v___x_4693_, 1, v_c_4692_);
                        v___x_4694_ = lean_nat_add(v_x_4664_, v___x_4667_);
                        crate::leanh::lean_dec(v_x_4664_);
                        v_j_4695_ = lean_array_get_size(v_as_4662_);
                        v_as_4696_ = lean_array_push(v_as_4662_, v___x_4693_);
                        v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            crate::leanh::lean_box(0),
                            v___x_4694_,
                            v_as_4696_,
                            v_j_4695_,
                        );
                        crate::leanh::lean_dec(v___x_4694_);
                        return v___x_4697_;
                    }
                }
            }
            1 => {
                v___x_4678_ = crate::leanh::lean_box(0);
                v_xs_x27_4679_ = lean_array_fset(v_as_4662_, v_mid_4668_, v___x_4678_);
                v___x_4680_ = lean_nat_add(v_x_4658_, v___x_4667_);
                v_c_4681_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4659_, v_v_4660_, v___x_4680_, v_snd_4674_);
                crate::leanh::lean_dec(v___x_4680_);
                if v_isShared_4677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4676_, 1, v_c_4681_);
                    crate::leanh::lean_ctor_set(v___x_4676_, 0, v_k_4661_);
                    v___x_4683_ = v___x_4676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_k_4661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_c_4681_);
                    v___x_4683_ = v_reuseFailAlloc_4685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4684_ = lean_array_fset(v_xs_x27_4679_, v_mid_4668_, v___x_4683_);
                crate::leanh::lean_dec(v_mid_4668_);
                return v___x_4684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(
    mut v_x_4698_: *mut crate::leanh::LeanObject,
    mut v_keys_4699_: *mut crate::leanh::LeanObject,
    mut v_v_4700_: *mut crate::leanh::LeanObject,
    mut v_k_4701_: *mut crate::leanh::LeanObject,
    mut v_as_4702_: *mut crate::leanh::LeanObject,
    mut v_k_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: u8 = 0;
    v___x_4704_ = lean_array_get_size(v_as_4702_);
    v___x_4705_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4706_ = lean_nat_dec_eq(v___x_4704_, v___x_4705_);
    if v___x_4706_ == 0 {
        let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v_k_4701_);
                    crate::leanh::lean_dec_ref(v_v_4700_);
                    return v_as_4702_;
                } else {
                    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc(v___x_4707_);
                    v___x_4711_ = crate::leanh::lean_box(0);
                    v_xs_x27_4712_ = lean_array_fset(v_as_4702_, v___x_4705_, v___x_4711_);
                    v___x_4713_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4707_);
                    v___x_4714_ = lean_array_fset(v_xs_x27_4712_, v___x_4705_, v___x_4713_);
                    return v___x_4714_;
                }
            } else {
                let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4718_: u8 = 0;
                v___x_4715_ = crate::leanh::lean_unsigned_to_nat(1);
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
                            crate::leanh::lean_dec(v___x_4716_);
                            crate::leanh::lean_dec(v_k_4701_);
                            crate::leanh::lean_dec_ref(v_v_4700_);
                            return v_as_4702_;
                        } else {
                            let mut v___x_4721_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_4722_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4723_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4724_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_inc(v___x_4717_);
                            v___x_4721_ = crate::leanh::lean_box(0);
                            v_xs_x27_4722_ = lean_array_fset(v_as_4702_, v___x_4716_, v___x_4721_);
                            v___x_4723_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4717_);
                            v___x_4724_ = lean_array_fset(v_xs_x27_4722_, v___x_4716_, v___x_4723_);
                            crate::leanh::lean_dec(v___x_4716_);
                            return v___x_4724_;
                        }
                    } else {
                        let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_4725_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v_as_4702_, v_k_4703_, v___x_4705_, v___x_4716_);
                        return v___x_4725_;
                    }
                } else {
                    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_4716_);
                    v___x_4726_ = crate::leanh::lean_box(0);
                    v___x_4727_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4726_);
                    v___x_4728_ = lean_array_push(v_as_4702_, v___x_4727_);
                    return v___x_4728_;
                }
            }
        } else {
            let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_as_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4729_ = crate::leanh::lean_box(0);
            v___x_4730_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4729_);
            v_as_4731_ = lean_array_push(v_as_4702_, v___x_4730_);
            v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                crate::leanh::lean_box(0),
                v___x_4705_,
                v_as_4731_,
                v___x_4704_,
            );
            return v___x_4732_;
        }
    } else {
        let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4733_ = crate::leanh::lean_box(0);
        v___x_4734_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__0(v_x_4698_, v_keys_4699_, v_v_4700_, v_k_4701_, v___x_4733_);
        v___x_4735_ = lean_array_push(v_as_4702_, v___x_4734_);
        return v___x_4735_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(
    mut v_keys_4736_: *mut crate::leanh::LeanObject,
    mut v_v_4737_: *mut crate::leanh::LeanObject,
    mut v_x_4738_: *mut crate::leanh::LeanObject,
    mut v_x_4739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vs_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4744_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_4740_ = crate::leanh::lean_ctor_get(v_x_4739_, 0);
                v_children_4741_ = crate::leanh::lean_ctor_get(v_x_4739_, 1);
                v_isSharedCheck_4758_ = (!crate::leanh::lean_is_exclusive(v_x_4739_)) as u8;
                if v_isSharedCheck_4758_ == 0 {
                    v___x_4743_ = v_x_4739_;
                    v_isShared_4744_ = v_isSharedCheck_4758_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_children_4741_);
                    crate::leanh::lean_inc(v_vs_4740_);
                    crate::leanh::lean_dec(v_x_4739_);
                    v___x_4743_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_4743_, 0, v___x_4747_);
                        v___x_4749_ = v___x_4743_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_children_4741_);
                        v___x_4749_ = v_reuseFailAlloc_4750_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_4751_ = lean_array_fget_borrowed(v_keys_4736_, v_x_4738_);
                    v___x_4752_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___closed__1;
                    crate::leanh::lean_inc_n(v_k_4751_, 2);
                    v___x_4753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4753_, 0, v_k_4751_);
                    crate::leanh::lean_ctor_set(v___x_4753_, 1, v___x_4752_);
                    v_c_4754_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_4738_, v_keys_4736_, v_v_4737_, v_k_4751_, v_children_4741_, v___x_4753_);
                    crate::leanh::lean_dec_ref_known(v___x_4753_, 2);
                    if v_isShared_4744_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4743_, 1, v_c_4754_);
                        v___x_4756_ = v___x_4743_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4757_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_vs_4740_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_c_4754_);
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
    mut v_x_4759_: *mut crate::leanh::LeanObject,
    mut v_keys_4760_: *mut crate::leanh::LeanObject,
    mut v_v_4761_: *mut crate::leanh::LeanObject,
    mut v_k_4762_: *mut crate::leanh::LeanObject,
    mut v_x_4763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4767_: u8 = 0;
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_unused_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4764_ = crate::leanh::lean_ctor_get(v_x_4763_, 1);
                v_isSharedCheck_4774_ = (!crate::leanh::lean_is_exclusive(v_x_4763_)) as u8;
                if v_isSharedCheck_4774_ == 0 {
                    v_unused_4775_ = crate::leanh::lean_ctor_get(v_x_4763_, 0);
                    crate::leanh::lean_dec(v_unused_4775_);
                    v___x_4766_ = v_x_4763_;
                    v_isShared_4767_ = v_isSharedCheck_4774_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4764_);
                    crate::leanh::lean_dec(v_x_4763_);
                    v___x_4766_ = crate::leanh::lean_box(0);
                    v_isShared_4767_ = v_isSharedCheck_4774_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4768_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4769_ = lean_nat_add(v_x_4759_, v___x_4768_);
                v_c_4770_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4760_, v_v_4761_, v___x_4769_, v_snd_4764_);
                crate::leanh::lean_dec(v___x_4769_);
                if v_isShared_4767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4766_, 1, v_c_4770_);
                    crate::leanh::lean_ctor_set(v___x_4766_, 0, v_k_4762_);
                    v___x_4772_ = v___x_4766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_k_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_c_4770_);
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
    mut v_x_4776_: *mut crate::leanh::LeanObject,
    mut v_keys_4777_: *mut crate::leanh::LeanObject,
    mut v_v_4778_: *mut crate::leanh::LeanObject,
    mut v_k_4779_: *mut crate::leanh::LeanObject,
    mut v_x_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___lam__2(v_x_4776_, v_keys_4777_, v_v_4778_, v_k_4779_, v_x_4780_);
    crate::leanh::lean_dec_ref(v_keys_4777_);
    crate::leanh::lean_dec(v_x_4776_);
    return v_res_4781_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2___boxed(
    mut v_keys_4782_: *mut crate::leanh::LeanObject,
    mut v_v_4783_: *mut crate::leanh::LeanObject,
    mut v_x_4784_: *mut crate::leanh::LeanObject,
    mut v_x_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4786_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4782_, v_v_4783_, v_x_4784_, v_x_4785_);
    crate::leanh::lean_dec(v_x_4784_);
    crate::leanh::lean_dec_ref(v_keys_4782_);
    return v_res_4786_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_x_4787_: *mut crate::leanh::LeanObject,
    mut v_keys_4788_: *mut crate::leanh::LeanObject,
    mut v_v_4789_: *mut crate::leanh::LeanObject,
    mut v_k_4790_: *mut crate::leanh::LeanObject,
    mut v_as_4791_: *mut crate::leanh::LeanObject,
    mut v_k_4792_: *mut crate::leanh::LeanObject,
    mut v_x_4793_: *mut crate::leanh::LeanObject,
    mut v_x_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4795_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_4787_, v_keys_4788_, v_v_4789_, v_k_4790_, v_as_4791_, v_k_4792_, v_x_4793_, v_x_4794_);
    crate::leanh::lean_dec_ref(v_k_4792_);
    crate::leanh::lean_dec_ref(v_keys_4788_);
    crate::leanh::lean_dec(v_x_4787_);
    return v_res_4795_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6___boxed(
    mut v_x_4796_: *mut crate::leanh::LeanObject,
    mut v_keys_4797_: *mut crate::leanh::LeanObject,
    mut v_v_4798_: *mut crate::leanh::LeanObject,
    mut v_k_4799_: *mut crate::leanh::LeanObject,
    mut v_as_4800_: *mut crate::leanh::LeanObject,
    mut v_k_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6(v_x_4796_, v_keys_4797_, v_v_4798_, v_k_4799_, v_as_4800_, v_k_4801_);
    crate::leanh::lean_dec_ref(v_k_4801_);
    crate::leanh::lean_dec_ref(v_keys_4797_);
    crate::leanh::lean_dec(v_x_4796_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_4803_: *mut crate::leanh::LeanObject,
    mut v_vals_4804_: *mut crate::leanh::LeanObject,
    mut v_i_4805_: *mut crate::leanh::LeanObject,
    mut v_k_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: u8 = 0;
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4807_ = lean_array_get_size(v_keys_4803_);
                v___x_4808_ = lean_nat_dec_lt(v_i_4805_, v___x_4807_);
                if v___x_4808_ == 0 {
                    crate::leanh::lean_dec(v_i_4805_);
                    v___x_4809_ = crate::leanh::lean_box(0);
                    return v___x_4809_;
                } else {
                    v_k_x27_4810_ = lean_array_fget_borrowed(v_keys_4803_, v_i_4805_);
                    v___x_4811_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_4806_, v_k_x27_4810_);
                    if v___x_4811_ == 0 {
                        v___x_4812_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4813_ = lean_nat_add(v_i_4805_, v___x_4812_);
                        crate::leanh::lean_dec(v_i_4805_);
                        v_i_4805_ = v___x_4813_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4815_ = lean_array_fget_borrowed(v_vals_4804_, v_i_4805_);
                        crate::leanh::lean_dec(v_i_4805_);
                        crate::leanh::lean_inc(v___x_4815_);
                        v___x_4816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4816_, 0, v___x_4815_);
                        return v___x_4816_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_4817_: *mut crate::leanh::LeanObject,
    mut v_vals_4818_: *mut crate::leanh::LeanObject,
    mut v_i_4819_: *mut crate::leanh::LeanObject,
    mut v_k_4820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4821_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_4817_, v_vals_4818_, v_i_4819_, v_k_4820_);
    crate::leanh::lean_dec(v_k_4820_);
    crate::leanh::lean_dec_ref(v_vals_4818_);
    crate::leanh::lean_dec_ref(v_keys_4817_);
    return v_res_4821_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(
    mut v_x_4822_: *mut crate::leanh::LeanObject,
    mut v_x_4823_: usize,
    mut v_x_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4829_: usize = 0;
    let mut v_j_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: u8 = 0;
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: usize = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4822_) == 0 {
                    v_es_4825_ = crate::leanh::lean_ctor_get(v_x_4822_, 0);
                    v___x_4826_ = crate::leanh::lean_box(2);
                    v___x_4827_ = 5usize;
                    v___x_4828_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4829_ = lean_usize_land(v_x_4823_, v___x_4828_);
                    v_j_4830_ = lean_usize_to_nat(v___x_4829_);
                    v___x_4831_ = lean_array_get_borrowed(v___x_4826_, v_es_4825_, v_j_4830_);
                    crate::leanh::lean_dec(v_j_4830_);
                    match crate::leanh::lean_obj_tag(v___x_4831_) {
                        0 => {
                            v_key_4832_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
                            v_val_4833_ = crate::leanh::lean_ctor_get(v___x_4831_, 1);
                            v___x_4834_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4824_, v_key_4832_);
                            if v___x_4834_ == 0 {
                                v___x_4835_ = crate::leanh::lean_box(0);
                                return v___x_4835_;
                            } else {
                                crate::leanh::lean_inc(v_val_4833_);
                                v___x_4836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4836_, 0, v_val_4833_);
                                return v___x_4836_;
                            }
                        }
                        1 => {
                            v_node_4837_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
                            v___x_4838_ = lean_usize_shift_right(v_x_4823_, v___x_4827_);
                            v_x_4822_ = v_node_4837_;
                            v_x_4823_ = v___x_4838_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4840_ = crate::leanh::lean_box(0);
                            return v___x_4840_;
                        }
                    }
                } else {
                    v_ks_4841_ = crate::leanh::lean_ctor_get(v_x_4822_, 0);
                    v_vs_4842_ = crate::leanh::lean_ctor_get(v_x_4822_, 1);
                    v___x_4843_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4844_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_4841_, v_vs_4842_, v___x_4843_, v_x_4824_);
                    return v___x_4844_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4845_: *mut crate::leanh::LeanObject,
    mut v_x_4846_: *mut crate::leanh::LeanObject,
    mut v_x_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2045__boxed_4848_: usize = 0;
    let mut v_res_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2045__boxed_4848_ = crate::leanh::lean_unbox_usize(v_x_4846_);
    crate::leanh::lean_dec(v_x_4846_);
    v_res_4849_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_4845_, v_x_2045__boxed_4848_, v_x_4847_);
    crate::leanh::lean_dec(v_x_4847_);
    crate::leanh::lean_dec_ref(v_x_4845_);
    return v_res_4849_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(
    mut v_x_4850_: *mut crate::leanh::LeanObject,
    mut v_x_4851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4852_: u64 = 0;
    let mut v___x_4853_: usize = 0;
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4852_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4851_);
    v___x_4853_ = lean_uint64_to_usize(v___x_4852_);
    v___x_4854_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_4850_, v___x_4853_, v_x_4851_);
    return v___x_4854_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_4855_: *mut crate::leanh::LeanObject,
    mut v_x_4856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4857_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_4855_, v_x_4856_);
    crate::leanh::lean_dec(v_x_4856_);
    crate::leanh::lean_dec_ref(v_x_4855_);
    return v_res_4857_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4858_ = l_Lean_Meta_DiscrTree_instInhabited(crate::leanh::lean_box(0));
    return v___x_4858_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(
    mut v_msg_4859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4860_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3___closed__0);
    v___x_4861_ = lean_panic_fn_borrowed(v___x_4860_, v_msg_4859_);
    return v___x_4861_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4865_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__2;
    v___x_4866_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_4867_ = crate::leanh::lean_unsigned_to_nat(166);
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
    mut v_d_4871_: *mut crate::leanh::LeanObject,
    mut v_keys_4872_: *mut crate::leanh::LeanObject,
    mut v_v_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    v___x_4874_ = lean_array_get_size(v_keys_4872_);
    v___x_4875_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4876_ = lean_nat_dec_eq(v___x_4874_, v___x_4875_);
    if v___x_4876_ == 0 {
        let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4877_ = crate::leanh::lean_box(0);
        v_k_4878_ = lean_array_get_borrowed(v___x_4877_, v_keys_4872_, v___x_4875_);
        v___x_4879_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_d_4871_, v_k_4878_);
        if crate::leanh::lean_obj_tag(v___x_4879_) == 0 {
            let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4880_ = crate::leanh::lean_unsigned_to_nat(1);
            v_c_4881_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                crate::leanh::lean_box(0),
                v_keys_4872_,
                v_v_4873_,
                v___x_4880_,
            );
            crate::leanh::lean_inc(v_k_4878_);
            v___x_4882_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_4871_, v_k_4878_, v_c_4881_);
            return v___x_4882_;
        } else {
            let mut v_val_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_4883_ = crate::leanh::lean_ctor_get(v___x_4879_, 0);
            crate::leanh::lean_inc(v_val_4883_);
            crate::leanh::lean_dec_ref_known(v___x_4879_, 1);
            v___x_4884_ = crate::leanh::lean_unsigned_to_nat(1);
            v_c_4885_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2(v_keys_4872_, v_v_4873_, v___x_4884_, v_val_4883_);
            crate::leanh::lean_inc(v_k_4878_);
            v___x_4886_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_d_4871_, v_k_4878_, v_c_4885_);
            return v___x_4886_;
        }
    } else {
        let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_v_4873_);
        crate::leanh::lean_dec_ref(v_d_4871_);
        v___x_4887_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___closed__3);
        v___x_4888_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__3(v___x_4887_);
        return v___x_4888_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0___boxed(
    mut v_d_4889_: *mut crate::leanh::LeanObject,
    mut v_keys_4890_: *mut crate::leanh::LeanObject,
    mut v_v_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_d_4889_, v_keys_4890_, v_v_4891_);
    crate::leanh::lean_dec_ref(v_keys_4890_);
    return v_res_4892_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(
    mut v_d_4893_: *mut crate::leanh::LeanObject,
    mut v_e_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_specs_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v_keys_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_4895_ = crate::leanh::lean_ctor_get(v_d_4893_, 0);
                v_erased_4896_ = crate::leanh::lean_ctor_get(v_d_4893_, 1);
                v_isSharedCheck_4905_ = (!crate::leanh::lean_is_exclusive(v_d_4893_)) as u8;
                if v_isSharedCheck_4905_ == 0 {
                    v___x_4898_ = v_d_4893_;
                    v_isShared_4899_ = v_isSharedCheck_4905_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_erased_4896_);
                    crate::leanh::lean_inc(v_specs_4895_);
                    crate::leanh::lean_dec(v_d_4893_);
                    v___x_4898_ = crate::leanh::lean_box(0);
                    v_isShared_4899_ = v_isSharedCheck_4905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keys_4900_ = crate::leanh::lean_ctor_get(v_e_4894_, 0);
                crate::leanh::lean_inc_ref(v_keys_4900_);
                v___x_4901_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0(v_specs_4895_, v_keys_4900_, v_e_4894_);
                crate::leanh::lean_dec_ref(v_keys_4900_);
                if v_isShared_4899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4898_, 0, v___x_4901_);
                    v___x_4903_ = v___x_4898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_erased_4896_);
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
    mut v_00_u03b2_4906_: *mut crate::leanh::LeanObject,
    mut v_x_4907_: *mut crate::leanh::LeanObject,
    mut v_x_4908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4909_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___redArg(v_x_4907_, v_x_4908_);
    return v___x_4909_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_4910_: *mut crate::leanh::LeanObject,
    mut v_x_4911_: *mut crate::leanh::LeanObject,
    mut v_x_4912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0(v_00_u03b2_4910_, v_x_4911_, v_x_4912_);
    crate::leanh::lean_dec(v_x_4912_);
    crate::leanh::lean_dec_ref(v_x_4911_);
    return v_res_4913_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1(
    mut v_00_u03b2_4914_: *mut crate::leanh::LeanObject,
    mut v_x_4915_: *mut crate::leanh::LeanObject,
    mut v_x_4916_: *mut crate::leanh::LeanObject,
    mut v_x_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4918_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1___redArg(v_x_4915_, v_x_4916_, v_x_4917_);
    return v___x_4918_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4919_: *mut crate::leanh::LeanObject,
    mut v_x_4920_: *mut crate::leanh::LeanObject,
    mut v_x_4921_: usize,
    mut v_x_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___redArg(v_x_4920_, v_x_4921_, v_x_4922_);
    return v___x_4923_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4924_: *mut crate::leanh::LeanObject,
    mut v_x_4925_: *mut crate::leanh::LeanObject,
    mut v_x_4926_: *mut crate::leanh::LeanObject,
    mut v_x_4927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2196__boxed_4928_: usize = 0;
    let mut v_res_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2196__boxed_4928_ = crate::leanh::lean_unbox_usize(v_x_4926_);
    crate::leanh::lean_dec(v_x_4926_);
    v_res_4929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1(v_00_u03b2_4924_, v_x_4925_, v_x_2196__boxed_4928_, v_x_4927_);
    crate::leanh::lean_dec(v_x_4927_);
    crate::leanh::lean_dec_ref(v_x_4925_);
    return v_res_4929_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4930_: *mut crate::leanh::LeanObject,
    mut v_x_4931_: *mut crate::leanh::LeanObject,
    mut v_x_4932_: usize,
    mut v_x_4933_: usize,
    mut v_x_4934_: *mut crate::leanh::LeanObject,
    mut v_x_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg(v_x_4931_, v_x_4932_, v_x_4933_, v_x_4934_, v_x_4935_);
    return v___x_4936_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4937_: *mut crate::leanh::LeanObject,
    mut v_x_4938_: *mut crate::leanh::LeanObject,
    mut v_x_4939_: *mut crate::leanh::LeanObject,
    mut v_x_4940_: *mut crate::leanh::LeanObject,
    mut v_x_4941_: *mut crate::leanh::LeanObject,
    mut v_x_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2207__boxed_4943_: usize = 0;
    let mut v_x_2208__boxed_4944_: usize = 0;
    let mut v_res_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2207__boxed_4943_ = crate::leanh::lean_unbox_usize(v_x_4939_);
    crate::leanh::lean_dec(v_x_4939_);
    v_x_2208__boxed_4944_ = crate::leanh::lean_unbox_usize(v_x_4940_);
    crate::leanh::lean_dec(v_x_4940_);
    v_res_4945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3(v_00_u03b2_4937_, v_x_4938_, v_x_2207__boxed_4943_, v_x_2208__boxed_4944_, v_x_4941_, v_x_4942_);
    return v_res_4945_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4946_: *mut crate::leanh::LeanObject,
    mut v_keys_4947_: *mut crate::leanh::LeanObject,
    mut v_vals_4948_: *mut crate::leanh::LeanObject,
    mut v_heq_4949_: *mut crate::leanh::LeanObject,
    mut v_i_4950_: *mut crate::leanh::LeanObject,
    mut v_k_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4952_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_4947_, v_vals_4948_, v_i_4950_, v_k_4951_);
    return v___x_4952_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4953_: *mut crate::leanh::LeanObject,
    mut v_keys_4954_: *mut crate::leanh::LeanObject,
    mut v_vals_4955_: *mut crate::leanh::LeanObject,
    mut v_heq_4956_: *mut crate::leanh::LeanObject,
    mut v_i_4957_: *mut crate::leanh::LeanObject,
    mut v_k_4958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4959_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4953_, v_keys_4954_, v_vals_4955_, v_heq_4956_, v_i_4957_, v_k_4958_);
    crate::leanh::lean_dec(v_k_4958_);
    crate::leanh::lean_dec_ref(v_vals_4955_);
    crate::leanh::lean_dec_ref(v_keys_4954_);
    return v_res_4959_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4960_: *mut crate::leanh::LeanObject,
    mut v_n_4961_: *mut crate::leanh::LeanObject,
    mut v_k_4962_: *mut crate::leanh::LeanObject,
    mut v_v_4963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4964_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6___redArg(v_n_4961_, v_k_4962_, v_v_4963_);
    return v___x_4964_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_4965_: *mut crate::leanh::LeanObject,
    mut v_depth_4966_: usize,
    mut v_keys_4967_: *mut crate::leanh::LeanObject,
    mut v_vals_4968_: *mut crate::leanh::LeanObject,
    mut v_heq_4969_: *mut crate::leanh::LeanObject,
    mut v_i_4970_: *mut crate::leanh::LeanObject,
    mut v_entries_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4972_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_4966_, v_keys_4967_, v_vals_4968_, v_i_4970_, v_entries_4971_);
    return v___x_4972_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_4973_: *mut crate::leanh::LeanObject,
    mut v_depth_4974_: *mut crate::leanh::LeanObject,
    mut v_keys_4975_: *mut crate::leanh::LeanObject,
    mut v_vals_4976_: *mut crate::leanh::LeanObject,
    mut v_heq_4977_: *mut crate::leanh::LeanObject,
    mut v_i_4978_: *mut crate::leanh::LeanObject,
    mut v_entries_4979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4980_ = crate::leanh::lean_unbox_usize(v_depth_4974_);
    crate::leanh::lean_dec(v_depth_4974_);
    v_res_4981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_4973_, v_depth_boxed_4980_, v_keys_4975_, v_vals_4976_, v_heq_4977_, v_i_4978_, v_entries_4979_);
    crate::leanh::lean_dec_ref(v_vals_4976_);
    crate::leanh::lean_dec_ref(v_keys_4975_);
    return v_res_4981_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(
    mut v_x_4982_: *mut crate::leanh::LeanObject,
    mut v_keys_4983_: *mut crate::leanh::LeanObject,
    mut v_v_4984_: *mut crate::leanh::LeanObject,
    mut v_k_4985_: *mut crate::leanh::LeanObject,
    mut v_as_4986_: *mut crate::leanh::LeanObject,
    mut v_k_4987_: *mut crate::leanh::LeanObject,
    mut v_x_4988_: *mut crate::leanh::LeanObject,
    mut v_x_4989_: *mut crate::leanh::LeanObject,
    mut v_x_4990_: *mut crate::leanh::LeanObject,
    mut v_x_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4992_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___redArg(v_x_4982_, v_keys_4983_, v_v_4984_, v_k_4985_, v_as_4986_, v_k_4987_, v_x_4988_, v_x_4989_);
    return v___x_4992_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_x_4993_: *mut crate::leanh::LeanObject,
    mut v_keys_4994_: *mut crate::leanh::LeanObject,
    mut v_v_4995_: *mut crate::leanh::LeanObject,
    mut v_k_4996_: *mut crate::leanh::LeanObject,
    mut v_as_4997_: *mut crate::leanh::LeanObject,
    mut v_k_4998_: *mut crate::leanh::LeanObject,
    mut v_x_4999_: *mut crate::leanh::LeanObject,
    mut v_x_5000_: *mut crate::leanh::LeanObject,
    mut v_x_5001_: *mut crate::leanh::LeanObject,
    mut v_x_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5003_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__2_spec__6_spec__12(v_x_4993_, v_keys_4994_, v_v_4995_, v_k_4996_, v_as_4997_, v_k_4998_, v_x_4999_, v_x_5000_, v_x_5001_, v_x_5002_);
    crate::leanh::lean_dec_ref(v_k_4998_);
    crate::leanh::lean_dec_ref(v_keys_4994_);
    crate::leanh::lean_dec(v_x_4993_);
    return v_res_5003_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_5004_: *mut crate::leanh::LeanObject,
    mut v_x_5005_: *mut crate::leanh::LeanObject,
    mut v_x_5006_: *mut crate::leanh::LeanObject,
    mut v_x_5007_: *mut crate::leanh::LeanObject,
    mut v_x_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5009_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_5005_, v_x_5006_, v_x_5007_, v_x_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(
    mut v_keys_5010_: *mut crate::leanh::LeanObject,
    mut v_i_5011_: *mut crate::leanh::LeanObject,
    mut v_k_5012_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: u8 = 0;
    let mut v_k_x27_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5013_ = lean_array_get_size(v_keys_5010_);
                v___x_5014_ = lean_nat_dec_lt(v_i_5011_, v___x_5013_);
                if v___x_5014_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_5012_);
                    crate::leanh::lean_dec(v_i_5011_);
                    return v___x_5014_;
                } else {
                    v_k_x27_5015_ = lean_array_fget_borrowed(v_keys_5010_, v_i_5011_);
                    crate::leanh::lean_inc(v_k_x27_5015_);
                    crate::leanh::lean_inc_ref(v_k_5012_);
                    v___x_5016_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_k_5012_,
                        v_k_x27_5015_,
                    );
                    if v___x_5016_ == 0 {
                        v___x_5017_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5018_ = lean_nat_add(v_i_5011_, v___x_5017_);
                        crate::leanh::lean_dec(v_i_5011_);
                        v_i_5011_ = v___x_5018_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5012_);
                        crate::leanh::lean_dec(v_i_5011_);
                        return v___x_5016_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_5020_: *mut crate::leanh::LeanObject,
    mut v_i_5021_: *mut crate::leanh::LeanObject,
    mut v_k_5022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5023_: u8 = 0;
    let mut v_r_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5023_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_5020_, v_i_5021_, v_k_5022_);
    crate::leanh::lean_dec_ref(v_keys_5020_);
    v_r_5024_ = crate::leanh::lean_box((v_res_5023_) as usize);
    return v_r_5024_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(
    mut v_x_5025_: *mut crate::leanh::LeanObject,
    mut v_x_5026_: usize,
    mut v_x_5027_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: usize = 0;
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: usize = 0;
    let mut v_j_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v_node_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: usize = 0;
    let mut v___x_5040_: u8 = 0;
    let mut v_ks_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5025_) == 0 {
                    v_es_5028_ = crate::leanh::lean_ctor_get(v_x_5025_, 0);
                    crate::leanh::lean_inc_ref(v_es_5028_);
                    crate::leanh::lean_dec_ref_known(v_x_5025_, 1);
                    v___x_5029_ = crate::leanh::lean_box(2);
                    v___x_5030_ = 5usize;
                    v___x_5031_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_5032_ = lean_usize_land(v_x_5026_, v___x_5031_);
                    v_j_5033_ = lean_usize_to_nat(v___x_5032_);
                    v___x_5034_ = lean_array_get(v___x_5029_, v_es_5028_, v_j_5033_);
                    crate::leanh::lean_dec(v_j_5033_);
                    crate::leanh::lean_dec_ref(v_es_5028_);
                    match crate::leanh::lean_obj_tag(v___x_5034_) {
                        0 => {
                            v_key_5035_ = crate::leanh::lean_ctor_get(v___x_5034_, 0);
                            crate::leanh::lean_inc(v_key_5035_);
                            crate::leanh::lean_dec_ref_known(v___x_5034_, 2);
                            v___x_5036_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                                v_x_5027_,
                                v_key_5035_,
                            );
                            return v___x_5036_;
                        }
                        1 => {
                            v_node_5037_ = crate::leanh::lean_ctor_get(v___x_5034_, 0);
                            crate::leanh::lean_inc(v_node_5037_);
                            crate::leanh::lean_dec_ref_known(v___x_5034_, 1);
                            v___x_5038_ = lean_usize_shift_right(v_x_5026_, v___x_5030_);
                            v_x_5025_ = v_node_5037_;
                            v_x_5026_ = v___x_5038_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_x_5027_);
                            v___x_5040_ = 0;
                            return v___x_5040_;
                        }
                    }
                } else {
                    v_ks_5041_ = crate::leanh::lean_ctor_get(v_x_5025_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5041_);
                    crate::leanh::lean_dec_ref_known(v_x_5025_, 2);
                    v___x_5042_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_ks_5041_, v___x_5042_, v_x_5027_);
                    crate::leanh::lean_dec_ref(v_ks_5041_);
                    return v___x_5043_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg___boxed(
    mut v_x_5044_: *mut crate::leanh::LeanObject,
    mut v_x_5045_: *mut crate::leanh::LeanObject,
    mut v_x_5046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_146__boxed_5047_: usize = 0;
    let mut v_res_5048_: u8 = 0;
    let mut v_r_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_146__boxed_5047_ = crate::leanh::lean_unbox_usize(v_x_5045_);
    crate::leanh::lean_dec(v_x_5045_);
    v_res_5048_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_5044_, v_x_146__boxed_5047_, v_x_5046_);
    v_r_5049_ = crate::leanh::lean_box((v_res_5048_) as usize);
    return v_r_5049_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(
    mut v_x_5050_: *mut crate::leanh::LeanObject,
    mut v_x_5051_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_5053_: u64 = 0;
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: u8 = 0;
    let mut v___y_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u64 = 0;
    let mut v_hash_5059_: u64 = 0;
    let mut v_declName_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_5060_ = crate::leanh::lean_ctor_get(v_x_5051_, 0);
                crate::leanh::lean_inc(v_declName_5060_);
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
                if crate::leanh::lean_obj_tag(v___y_5057_) == 0 {
                    v___x_5058_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    v___y_5053_ = v___x_5058_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5059_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_5057_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___y_5057_);
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
    mut v_x_5061_: *mut crate::leanh::LeanObject,
    mut v_x_5062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5063_: u8 = 0;
    let mut v_r_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_5061_, v_x_5062_);
    v_r_5064_ = crate::leanh::lean_box((v_res_5063_) as usize);
    return v_r_5064_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(
    mut v_d_5065_: *mut crate::leanh::LeanObject,
    mut v_thmId_5066_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_erased_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: u8 = 0;
    v_erased_5067_ = crate::leanh::lean_ctor_get(v_d_5065_, 1);
    crate::leanh::lean_inc_ref(v_erased_5067_);
    crate::leanh::lean_dec_ref(v_d_5065_);
    v___x_5068_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_erased_5067_, v_thmId_5066_);
    return v___x_5068_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased___boxed(
    mut v_d_5069_: *mut crate::leanh::LeanObject,
    mut v_thmId_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5071_: u8 = 0;
    let mut v_r_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5071_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_d_5069_, v_thmId_5070_);
    v_r_5072_ = crate::leanh::lean_box((v_res_5071_) as usize);
    return v_r_5072_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(
    mut v_00_u03b2_5073_: *mut crate::leanh::LeanObject,
    mut v_x_5074_: *mut crate::leanh::LeanObject,
    mut v_x_5075_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5076_: u8 = 0;
    v___x_5076_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___redArg(v_x_5074_, v_x_5075_);
    return v___x_5076_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0___boxed(
    mut v_00_u03b2_5077_: *mut crate::leanh::LeanObject,
    mut v_x_5078_: *mut crate::leanh::LeanObject,
    mut v_x_5079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5080_: u8 = 0;
    let mut v_r_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5080_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0(v_00_u03b2_5077_, v_x_5078_, v_x_5079_);
    v_r_5081_ = crate::leanh::lean_box((v_res_5080_) as usize);
    return v_r_5081_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(
    mut v_00_u03b2_5082_: *mut crate::leanh::LeanObject,
    mut v_x_5083_: *mut crate::leanh::LeanObject,
    mut v_x_5084_: usize,
    mut v_x_5085_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5086_: u8 = 0;
    v___x_5086_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___redArg(v_x_5083_, v_x_5084_, v_x_5085_);
    return v___x_5086_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0___boxed(
    mut v_00_u03b2_5087_: *mut crate::leanh::LeanObject,
    mut v_x_5088_: *mut crate::leanh::LeanObject,
    mut v_x_5089_: *mut crate::leanh::LeanObject,
    mut v_x_5090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_228__boxed_5091_: usize = 0;
    let mut v_res_5092_: u8 = 0;
    let mut v_r_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_228__boxed_5091_ = crate::leanh::lean_unbox_usize(v_x_5089_);
    crate::leanh::lean_dec(v_x_5089_);
    v_res_5092_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0(v_00_u03b2_5087_, v_x_5088_, v_x_228__boxed_5091_, v_x_5090_);
    v_r_5093_ = crate::leanh::lean_box((v_res_5092_) as usize);
    return v_r_5093_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5094_: *mut crate::leanh::LeanObject,
    mut v_keys_5095_: *mut crate::leanh::LeanObject,
    mut v_vals_5096_: *mut crate::leanh::LeanObject,
    mut v_heq_5097_: *mut crate::leanh::LeanObject,
    mut v_i_5098_: *mut crate::leanh::LeanObject,
    mut v_k_5099_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5100_: u8 = 0;
    v___x_5100_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___redArg(v_keys_5095_, v_i_5098_, v_k_5099_);
    return v___x_5100_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5101_: *mut crate::leanh::LeanObject,
    mut v_keys_5102_: *mut crate::leanh::LeanObject,
    mut v_vals_5103_: *mut crate::leanh::LeanObject,
    mut v_heq_5104_: *mut crate::leanh::LeanObject,
    mut v_i_5105_: *mut crate::leanh::LeanObject,
    mut v_k_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5107_: u8 = 0;
    let mut v_r_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5107_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased_spec__0_spec__0_spec__1(v_00_u03b2_5101_, v_keys_5102_, v_vals_5103_, v_heq_5104_, v_i_5105_, v_k_5106_);
    crate::leanh::lean_dec_ref(v_vals_5103_);
    crate::leanh::lean_dec_ref(v_keys_5102_);
    v_r_5108_ = crate::leanh::lean_box((v_res_5107_) as usize);
    return v_r_5108_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_5109_: *mut crate::leanh::LeanObject,
    mut v_x_5110_: *mut crate::leanh::LeanObject,
    mut v_x_5111_: *mut crate::leanh::LeanObject,
    mut v_x_5112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5117_: u8 = 0;
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5113_ = crate::leanh::lean_ctor_get(v_x_5109_, 0);
                v_vs_5114_ = crate::leanh::lean_ctor_get(v_x_5109_, 1);
                v_isSharedCheck_5138_ = (!crate::leanh::lean_is_exclusive(v_x_5109_)) as u8;
                if v_isSharedCheck_5138_ == 0 {
                    v___x_5116_ = v_x_5109_;
                    v_isShared_5117_ = v_isSharedCheck_5138_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_5114_);
                    crate::leanh::lean_inc(v_ks_5113_);
                    crate::leanh::lean_dec(v_x_5109_);
                    v___x_5116_ = crate::leanh::lean_box(0);
                    v_isShared_5117_ = v_isSharedCheck_5138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5118_ = lean_array_get_size(v_ks_5113_);
                v___x_5119_ = lean_nat_dec_lt(v_x_5110_, v___x_5118_);
                if v___x_5119_ == 0 {
                    crate::leanh::lean_dec(v_x_5110_);
                    v___x_5120_ = lean_array_push(v_ks_5113_, v_x_5111_);
                    v___x_5121_ = lean_array_push(v_vs_5114_, v_x_5112_);
                    if v_isShared_5117_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5116_, 1, v___x_5121_);
                        crate::leanh::lean_ctor_set(v___x_5116_, 0, v___x_5120_);
                        v___x_5123_ = v___x_5116_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5124_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v___x_5120_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 1, v___x_5121_);
                        v___x_5123_ = v_reuseFailAlloc_5124_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5125_ = lean_array_fget_borrowed(v_ks_5113_, v_x_5110_);
                    crate::leanh::lean_inc(v_k_x27_5125_);
                    crate::leanh::lean_inc_ref(v_x_5111_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_ks_5113_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_vs_5114_);
                            v___x_5128_ = v_reuseFailAlloc_5132_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5133_ = lean_array_fset(v_ks_5113_, v_x_5110_, v_x_5111_);
                        v___x_5134_ = lean_array_fset(v_vs_5114_, v_x_5110_, v_x_5112_);
                        crate::leanh::lean_dec(v_x_5110_);
                        if v_isShared_5117_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5116_, 1, v___x_5134_);
                            crate::leanh::lean_ctor_set(v___x_5116_, 0, v___x_5133_);
                            v___x_5136_ = v___x_5116_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5137_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5133_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 1, v___x_5134_);
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
                v___x_5129_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5130_ = lean_nat_add(v_x_5110_, v___x_5129_);
                crate::leanh::lean_dec(v_x_5110_);
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
    mut v_n_5139_: *mut crate::leanh::LeanObject,
    mut v_k_5140_: *mut crate::leanh::LeanObject,
    mut v_v_5141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5142_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5143_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_n_5139_, v___x_5142_, v_k_5140_, v_v_5141_);
    return v___x_5143_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5144_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5144_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(
    mut v_x_5145_: *mut crate::leanh::LeanObject,
    mut v_x_5146_: usize,
    mut v_x_5147_: usize,
    mut v_x_5148_: *mut crate::leanh::LeanObject,
    mut v_x_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: usize = 0;
    let mut v___x_5152_: usize = 0;
    let mut v___x_5153_: usize = 0;
    let mut v___x_5154_: usize = 0;
    let mut v_j_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: u8 = 0;
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v_v_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5174_: u8 = 0;
    let mut v___x_5175_: u8 = 0;
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut v_node_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5185_: u8 = 0;
    let mut v___x_5186_: usize = 0;
    let mut v___x_5187_: usize = 0;
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v_unused_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5200_: u8 = 0;
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5205_: u8 = 0;
    let mut v_ks_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: u8 = 0;
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: u8 = 0;
    let mut v_reuseFailAlloc_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5145_) == 0 {
                    v_es_5150_ = crate::leanh::lean_ctor_get(v_x_5145_, 0);
                    v___x_5151_ = 5usize;
                    v___x_5152_ = 1usize;
                    v___x_5153_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_5154_ = lean_usize_land(v_x_5146_, v___x_5153_);
                    v_j_5155_ = lean_usize_to_nat(v___x_5154_);
                    v___x_5156_ = lean_array_get_size(v_es_5150_);
                    v___x_5157_ = lean_nat_dec_lt(v_j_5155_, v___x_5156_);
                    if v___x_5157_ == 0 {
                        crate::leanh::lean_dec(v_j_5155_);
                        crate::leanh::lean_dec(v_x_5149_);
                        crate::leanh::lean_dec_ref(v_x_5148_);
                        return v_x_5145_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_5150_);
                        v_isSharedCheck_5194_ = (!crate::leanh::lean_is_exclusive(v_x_5145_)) as u8;
                        if v_isSharedCheck_5194_ == 0 {
                            v_unused_5195_ = crate::leanh::lean_ctor_get(v_x_5145_, 0);
                            crate::leanh::lean_dec(v_unused_5195_);
                            v___x_5159_ = v_x_5145_;
                            v_isShared_5160_ = v_isSharedCheck_5194_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5145_);
                            v___x_5159_ = crate::leanh::lean_box(0);
                            v_isShared_5160_ = v_isSharedCheck_5194_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5196_ = crate::leanh::lean_ctor_get(v_x_5145_, 0);
                    v_vs_5197_ = crate::leanh::lean_ctor_get(v_x_5145_, 1);
                    v_isSharedCheck_5217_ = (!crate::leanh::lean_is_exclusive(v_x_5145_)) as u8;
                    if v_isSharedCheck_5217_ == 0 {
                        v___x_5199_ = v_x_5145_;
                        v_isShared_5200_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5197_);
                        crate::leanh::lean_inc(v_ks_5196_);
                        crate::leanh::lean_dec(v_x_5145_);
                        v___x_5199_ = crate::leanh::lean_box(0);
                        v_isShared_5200_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5161_ = lean_array_fget(v_es_5150_, v_j_5155_);
                v___x_5162_ = crate::leanh::lean_box(0);
                v_xs_x27_5163_ = lean_array_fset(v_es_5150_, v_j_5155_, v___x_5162_);
                match crate::leanh::lean_obj_tag(v_v_5161_) {
                    0 => {
                        v_key_5170_ = crate::leanh::lean_ctor_get(v_v_5161_, 0);
                        v_val_5171_ = crate::leanh::lean_ctor_get(v_v_5161_, 1);
                        v_isSharedCheck_5181_ = (!crate::leanh::lean_is_exclusive(v_v_5161_)) as u8;
                        if v_isSharedCheck_5181_ == 0 {
                            v___x_5173_ = v_v_5161_;
                            v_isShared_5174_ = v_isSharedCheck_5181_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5171_);
                            crate::leanh::lean_inc(v_key_5170_);
                            crate::leanh::lean_dec(v_v_5161_);
                            v___x_5173_ = crate::leanh::lean_box(0);
                            v_isShared_5174_ = v_isSharedCheck_5181_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5182_ = crate::leanh::lean_ctor_get(v_v_5161_, 0);
                        v_isSharedCheck_5192_ = (!crate::leanh::lean_is_exclusive(v_v_5161_)) as u8;
                        if v_isSharedCheck_5192_ == 0 {
                            v___x_5184_ = v_v_5161_;
                            v_isShared_5185_ = v_isSharedCheck_5192_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5182_);
                            crate::leanh::lean_dec(v_v_5161_);
                            v___x_5184_ = crate::leanh::lean_box(0);
                            v_isShared_5185_ = v_isSharedCheck_5192_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5193_, 0, v_x_5148_);
                        crate::leanh::lean_ctor_set(v___x_5193_, 1, v_x_5149_);
                        v___y_5165_ = v___x_5193_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5166_ = lean_array_fset(v_xs_x27_5163_, v_j_5155_, v___y_5165_);
                crate::leanh::lean_dec(v_j_5155_);
                if v_isShared_5160_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5159_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5159_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5168_;
            }
            4 => {
                crate::leanh::lean_inc(v_key_5170_);
                crate::leanh::lean_inc_ref(v_x_5148_);
                v___x_5175_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_5148_, v_key_5170_);
                if v___x_5175_ == 0 {
                    crate::leanh::lean_del_object(v___x_5173_);
                    v___x_5176_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5170_,
                        v_val_5171_,
                        v_x_5148_,
                        v_x_5149_,
                    );
                    v___x_5177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5177_, 0, v___x_5176_);
                    v___y_5165_ = v___x_5177_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5171_);
                    crate::leanh::lean_dec(v_key_5170_);
                    if v_isShared_5174_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5173_, 1, v_x_5149_);
                        crate::leanh::lean_ctor_set(v___x_5173_, 0, v_x_5148_);
                        v___x_5179_ = v___x_5173_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_x_5148_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_x_5149_);
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
                    crate::leanh::lean_ctor_set(v___x_5184_, 0, v___x_5188_);
                    v___x_5190_ = v___x_5184_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5188_);
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
                    v_reuseFailAlloc_5216_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_ks_5196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 1, v_vs_5197_);
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
                    v___x_5214_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5215_ = lean_nat_dec_lt(v___x_5213_, v___x_5214_);
                    crate::leanh::lean_dec(v___x_5213_);
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
                    v_ks_5206_ = crate::leanh::lean_ctor_get(v_newNode_5203_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5206_);
                    v_vs_5207_ = crate::leanh::lean_ctor_get(v_newNode_5203_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5207_);
                    crate::leanh::lean_dec_ref(v_newNode_5203_);
                    v___x_5208_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5209_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___closed__0);
                    v___x_5210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_x_5147_, v_ks_5206_, v_vs_5207_, v___x_5208_, v___x_5209_);
                    crate::leanh::lean_dec_ref(v_vs_5207_);
                    crate::leanh::lean_dec_ref(v_ks_5206_);
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
    mut v_keys_5219_: *mut crate::leanh::LeanObject,
    mut v_vals_5220_: *mut crate::leanh::LeanObject,
    mut v_i_5221_: *mut crate::leanh::LeanObject,
    mut v_entries_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    let mut v_k_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5228_: u64 = 0;
    let mut v_h_5229_: usize = 0;
    let mut v___x_5230_: usize = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: usize = 0;
    let mut v___x_5233_: usize = 0;
    let mut v___x_5234_: usize = 0;
    let mut v_h_5235_: usize = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u64 = 0;
    let mut v_hash_5242_: u64 = 0;
    let mut v_declName_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = lean_array_get_size(v_keys_5219_);
                v___x_5224_ = lean_nat_dec_lt(v_i_5221_, v___x_5223_);
                if v___x_5224_ == 0 {
                    crate::leanh::lean_dec(v_i_5221_);
                    return v_entries_5222_;
                } else {
                    v_k_5225_ = lean_array_fget_borrowed(v_keys_5219_, v_i_5221_);
                    v_v_5226_ = lean_array_fget_borrowed(v_vals_5220_, v_i_5221_);
                    v_declName_5243_ = crate::leanh::lean_ctor_get(v_k_5225_, 0);
                    crate::leanh::lean_inc(v_declName_5243_);
                    v___y_5240_ = v_declName_5243_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_h_5229_ = lean_uint64_to_usize(v___y_5228_);
                v___x_5230_ = 5usize;
                v___x_5231_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5232_ = 1usize;
                v___x_5233_ = lean_usize_sub(v_depth_5218_, v___x_5232_);
                v___x_5234_ = lean_usize_mul(v___x_5230_, v___x_5233_);
                v_h_5235_ = lean_usize_shift_right(v_h_5229_, v___x_5234_);
                v___x_5236_ = lean_nat_add(v_i_5221_, v___x_5231_);
                crate::leanh::lean_dec(v_i_5221_);
                crate::leanh::lean_inc(v_v_5226_);
                crate::leanh::lean_inc(v_k_5225_);
                v___x_5237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_entries_5222_, v_h_5235_, v_depth_5218_, v_k_5225_, v_v_5226_);
                v_i_5221_ = v___x_5236_;
                v_entries_5222_ = v___x_5237_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5240_) == 0 {
                    v___x_5241_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    v___y_5228_ = v___x_5241_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5242_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_5240_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___y_5240_);
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
    mut v_depth_5244_: *mut crate::leanh::LeanObject,
    mut v_keys_5245_: *mut crate::leanh::LeanObject,
    mut v_vals_5246_: *mut crate::leanh::LeanObject,
    mut v_i_5247_: *mut crate::leanh::LeanObject,
    mut v_entries_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5249_: usize = 0;
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5249_ = crate::leanh::lean_unbox_usize(v_depth_5244_);
    crate::leanh::lean_dec(v_depth_5244_);
    v_res_5250_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_5249_, v_keys_5245_, v_vals_5246_, v_i_5247_, v_entries_5248_);
    crate::leanh::lean_dec_ref(v_vals_5246_);
    crate::leanh::lean_dec_ref(v_keys_5245_);
    return v_res_5250_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg___boxed(
    mut v_x_5251_: *mut crate::leanh::LeanObject,
    mut v_x_5252_: *mut crate::leanh::LeanObject,
    mut v_x_5253_: *mut crate::leanh::LeanObject,
    mut v_x_5254_: *mut crate::leanh::LeanObject,
    mut v_x_5255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_400__boxed_5256_: usize = 0;
    let mut v_x_401__boxed_5257_: usize = 0;
    let mut v_res_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_400__boxed_5256_ = crate::leanh::lean_unbox_usize(v_x_5252_);
    crate::leanh::lean_dec(v_x_5252_);
    v_x_401__boxed_5257_ = crate::leanh::lean_unbox_usize(v_x_5253_);
    crate::leanh::lean_dec(v_x_5253_);
    v_res_5258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_5251_, v_x_400__boxed_5256_, v_x_401__boxed_5257_, v_x_5254_, v_x_5255_);
    return v_res_5258_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(
    mut v_x_5259_: *mut crate::leanh::LeanObject,
    mut v_x_5260_: *mut crate::leanh::LeanObject,
    mut v_x_5261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5263_: u64 = 0;
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: usize = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u64 = 0;
    let mut v_hash_5270_: u64 = 0;
    let mut v_declName_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_5271_ = crate::leanh::lean_ctor_get(v_x_5260_, 0);
                crate::leanh::lean_inc(v_declName_5271_);
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
                if crate::leanh::lean_obj_tag(v___y_5268_) == 0 {
                    v___x_5269_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instHashableSpecProof___lam__0___closed__0);
                    v___y_5263_ = v___x_5269_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5270_ = crate::leanh::lean_ctor_get_uint64(
                        v___y_5268_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___y_5268_);
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
    mut v_d_5272_: *mut crate::leanh::LeanObject,
    mut v_thmId_5273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_specs_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_5274_ = crate::leanh::lean_ctor_get(v_d_5272_, 0);
                v_erased_5275_ = crate::leanh::lean_ctor_get(v_d_5272_, 1);
                v_isSharedCheck_5284_ = (!crate::leanh::lean_is_exclusive(v_d_5272_)) as u8;
                if v_isSharedCheck_5284_ == 0 {
                    v___x_5277_ = v_d_5272_;
                    v_isShared_5278_ = v_isSharedCheck_5284_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_erased_5275_);
                    crate::leanh::lean_inc(v_specs_5274_);
                    crate::leanh::lean_dec(v_d_5272_);
                    v___x_5277_ = crate::leanh::lean_box(0);
                    v_isShared_5278_ = v_isSharedCheck_5284_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5279_ = crate::leanh::lean_box(0);
                v___x_5280_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_erased_5275_, v_thmId_5273_, v___x_5279_);
                if v_isShared_5278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5277_, 1, v___x_5280_);
                    v___x_5282_ = v___x_5277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_specs_5274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___x_5280_);
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
    mut v_00_u03b2_5285_: *mut crate::leanh::LeanObject,
    mut v_x_5286_: *mut crate::leanh::LeanObject,
    mut v_x_5287_: *mut crate::leanh::LeanObject,
    mut v_x_5288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5289_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0___redArg(v_x_5286_, v_x_5287_, v_x_5288_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(
    mut v_00_u03b2_5290_: *mut crate::leanh::LeanObject,
    mut v_x_5291_: *mut crate::leanh::LeanObject,
    mut v_x_5292_: usize,
    mut v_x_5293_: usize,
    mut v_x_5294_: *mut crate::leanh::LeanObject,
    mut v_x_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___redArg(v_x_5291_, v_x_5292_, v_x_5293_, v_x_5294_, v_x_5295_);
    return v___x_5296_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0___boxed(
    mut v_00_u03b2_5297_: *mut crate::leanh::LeanObject,
    mut v_x_5298_: *mut crate::leanh::LeanObject,
    mut v_x_5299_: *mut crate::leanh::LeanObject,
    mut v_x_5300_: *mut crate::leanh::LeanObject,
    mut v_x_5301_: *mut crate::leanh::LeanObject,
    mut v_x_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_618__boxed_5303_: usize = 0;
    let mut v_x_619__boxed_5304_: usize = 0;
    let mut v_res_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_618__boxed_5303_ = crate::leanh::lean_unbox_usize(v_x_5299_);
    crate::leanh::lean_dec(v_x_5299_);
    v_x_619__boxed_5304_ = crate::leanh::lean_unbox_usize(v_x_5300_);
    crate::leanh::lean_dec(v_x_5300_);
    v_res_5305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0(v_00_u03b2_5297_, v_x_5298_, v_x_618__boxed_5303_, v_x_619__boxed_5304_, v_x_5301_, v_x_5302_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5306_: *mut crate::leanh::LeanObject,
    mut v_n_5307_: *mut crate::leanh::LeanObject,
    mut v_k_5308_: *mut crate::leanh::LeanObject,
    mut v_v_5309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1___redArg(v_n_5307_, v_k_5308_, v_v_5309_);
    return v___x_5310_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5311_: *mut crate::leanh::LeanObject,
    mut v_depth_5312_: usize,
    mut v_keys_5313_: *mut crate::leanh::LeanObject,
    mut v_vals_5314_: *mut crate::leanh::LeanObject,
    mut v_heq_5315_: *mut crate::leanh::LeanObject,
    mut v_i_5316_: *mut crate::leanh::LeanObject,
    mut v_entries_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___redArg(v_depth_5312_, v_keys_5313_, v_vals_5314_, v_i_5316_, v_entries_5317_);
    return v___x_5318_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5319_: *mut crate::leanh::LeanObject,
    mut v_depth_5320_: *mut crate::leanh::LeanObject,
    mut v_keys_5321_: *mut crate::leanh::LeanObject,
    mut v_vals_5322_: *mut crate::leanh::LeanObject,
    mut v_heq_5323_: *mut crate::leanh::LeanObject,
    mut v_i_5324_: *mut crate::leanh::LeanObject,
    mut v_entries_5325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5326_: usize = 0;
    let mut v_res_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5326_ = crate::leanh::lean_unbox_usize(v_depth_5320_);
    crate::leanh::lean_dec(v_depth_5320_);
    v_res_5327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__2(v_00_u03b2_5319_, v_depth_boxed_5326_, v_keys_5321_, v_vals_5322_, v_heq_5323_, v_i_5324_, v_entries_5325_);
    crate::leanh::lean_dec_ref(v_vals_5322_);
    crate::leanh::lean_dec_ref(v_keys_5321_);
    return v_res_5327_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5328_: *mut crate::leanh::LeanObject,
    mut v_x_5329_: *mut crate::leanh::LeanObject,
    mut v_x_5330_: *mut crate::leanh::LeanObject,
    mut v_x_5331_: *mut crate::leanh::LeanObject,
    mut v_x_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5333_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase_spec__0_spec__0_spec__1_spec__2___redArg(v_x_5329_, v_x_5330_, v_x_5331_, v_x_5332_);
    return v___x_5333_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(
    mut v_a_5334_: *mut crate::leanh::LeanObject,
    mut v_as_5335_: *mut crate::leanh::LeanObject,
    mut v_i_5336_: usize,
    mut v_stop_5337_: usize,
) -> u8 {
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_5345_: *mut crate::leanh::LeanObject,
    mut v_as_5346_: *mut crate::leanh::LeanObject,
    mut v_i_5347_: *mut crate::leanh::LeanObject,
    mut v_stop_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5349_: usize = 0;
    let mut v_stop_boxed_5350_: usize = 0;
    let mut v_res_5351_: u8 = 0;
    let mut v_r_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5349_ = crate::leanh::lean_unbox_usize(v_i_5347_);
    crate::leanh::lean_dec(v_i_5347_);
    v_stop_boxed_5350_ = crate::leanh::lean_unbox_usize(v_stop_5348_);
    crate::leanh::lean_dec(v_stop_5348_);
    v_res_5351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0_spec__0(v_a_5345_, v_as_5346_, v_i_boxed_5349_, v_stop_boxed_5350_);
    crate::leanh::lean_dec_ref(v_as_5346_);
    crate::leanh::lean_dec_ref(v_a_5345_);
    v_r_5352_ = crate::leanh::lean_box((v_res_5351_) as usize);
    return v_r_5352_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(
    mut v_as_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: u8 = 0;
    v___x_5355_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_as_5361_: *mut crate::leanh::LeanObject,
    mut v_a_5362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5363_: u8 = 0;
    let mut v_r_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5363_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_as_5361_, v_a_5362_);
    crate::leanh::lean_dec_ref(v_a_5362_);
    crate::leanh::lean_dec_ref(v_as_5361_);
    v_r_5364_ = crate::leanh::lean_box((v_res_5363_) as usize);
    return v_r_5364_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(
    mut v_xs_5368_: *mut crate::leanh::LeanObject,
    mut v_e_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v_a_5372_: *mut crate::leanh::LeanObject,
    mut v_a_5373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ty_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5429_: u8 = 0;
    let mut v_l_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: u8 = 0;
    let mut v___x_5434_: u8 = 0;
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: u8 = 0;
    let mut v___y_5441_: u8 = 0;
    let mut v___x_5442_: u8 = 0;
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: u8 = 0;
    let mut v___x_5446_: u8 = 0;
    let mut v_binderType_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5462_: u8 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v_expr_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5394_ = l_Lean_Expr_hasExprMVar(v_e_5369_);
                if v___x_5394_ == 0 {
                    v___x_5395_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5396_, 0, v___x_5395_);
                    return v___x_5396_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_5369_) {
                        5 => {
                            v_fn_5397_ = crate::leanh::lean_ctor_get(v_e_5369_, 0);
                            v_arg_5398_ = crate::leanh::lean_ctor_get(v_e_5369_, 1);
                            v___x_5399_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go___closed__1;
                            v___x_5400_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_5401_ =
                                l_Lean_Expr_isAppOfArity(v_e_5369_, v___x_5399_, v___x_5400_);
                            if v___x_5401_ == 0 {
                                v___x_5402_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_fn_5397_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                if crate::leanh::lean_obj_tag(v___x_5402_) == 0 {
                                    v_a_5403_ = crate::leanh::lean_ctor_get(v___x_5402_, 0);
                                    crate::leanh::lean_inc(v_a_5403_);
                                    crate::leanh::lean_dec_ref_known(v___x_5402_, 1);
                                    v___x_5404_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_arg_5398_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                    if crate::leanh::lean_obj_tag(v___x_5404_) == 0 {
                                        v_a_5405_ = crate::leanh::lean_ctor_get(v___x_5404_, 0);
                                        v_isSharedCheck_5413_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5404_)) as u8;
                                        if v_isSharedCheck_5413_ == 0 {
                                            v___x_5407_ = v___x_5404_;
                                            v_isShared_5408_ = v_isSharedCheck_5413_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5405_);
                                            crate::leanh::lean_dec(v___x_5404_);
                                            v___x_5407_ = crate::leanh::lean_box(0);
                                            v_isShared_5408_ = v_isSharedCheck_5413_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5403_);
                                        return v___x_5404_;
                                    }
                                } else {
                                    return v___x_5402_;
                                }
                            } else {
                                v___x_5414_ = l_Lean_Expr_appFn_x21(v_e_5369_);
                                v___x_5415_ = l_Lean_Expr_appArg_x21(v___x_5414_);
                                crate::leanh::lean_dec_ref(v___x_5414_);
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
                            v_binderType_5447_ = crate::leanh::lean_ctor_get(v_e_5369_, 1);
                            v_body_5448_ = crate::leanh::lean_ctor_get(v_e_5369_, 2);
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
                            v_binderType_5449_ = crate::leanh::lean_ctor_get(v_e_5369_, 1);
                            v_body_5450_ = crate::leanh::lean_ctor_get(v_e_5369_, 2);
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
                            v_type_5451_ = crate::leanh::lean_ctor_get(v_e_5369_, 1);
                            v_value_5452_ = crate::leanh::lean_ctor_get(v_e_5369_, 2);
                            v_body_5453_ = crate::leanh::lean_ctor_get(v_e_5369_, 3);
                            v___x_5454_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_type_5451_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                            if crate::leanh::lean_obj_tag(v___x_5454_) == 0 {
                                v_a_5455_ = crate::leanh::lean_ctor_get(v___x_5454_, 0);
                                crate::leanh::lean_inc(v_a_5455_);
                                crate::leanh::lean_dec_ref_known(v___x_5454_, 1);
                                v___x_5456_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_value_5452_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                if crate::leanh::lean_obj_tag(v___x_5456_) == 0 {
                                    v_a_5457_ = crate::leanh::lean_ctor_get(v___x_5456_, 0);
                                    crate::leanh::lean_inc(v_a_5457_);
                                    crate::leanh::lean_dec_ref_known(v___x_5456_, 1);
                                    v___x_5458_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_body_5453_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                                    if crate::leanh::lean_obj_tag(v___x_5458_) == 0 {
                                        v_a_5459_ = crate::leanh::lean_ctor_get(v___x_5458_, 0);
                                        v_isSharedCheck_5468_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5458_)) as u8;
                                        if v_isSharedCheck_5468_ == 0 {
                                            v___x_5461_ = v___x_5458_;
                                            v_isShared_5462_ = v_isSharedCheck_5468_;
                                            state = 12;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5459_);
                                            crate::leanh::lean_dec(v___x_5458_);
                                            v___x_5461_ = crate::leanh::lean_box(0);
                                            v_isShared_5462_ = v_isSharedCheck_5468_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5457_);
                                        crate::leanh::lean_dec(v_a_5455_);
                                        return v___x_5458_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5455_);
                                    return v___x_5456_;
                                }
                            } else {
                                return v___x_5454_;
                            }
                        }
                        10 => {
                            v_expr_5469_ = crate::leanh::lean_ctor_get(v_e_5369_, 1);
                            v_e_5369_ = v_expr_5469_;
                            state = 0;
                            continue;
                        }
                        11 => {
                            v_struct_5471_ = crate::leanh::lean_ctor_get(v_e_5369_, 2);
                            v_e_5369_ = v_struct_5471_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5473_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_5474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5474_, 0, v___x_5473_);
                            return v___x_5474_;
                        }
                    }
                }
            }
            1 => {
                v___x_5382_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_ty_5376_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
                if crate::leanh::lean_obj_tag(v___x_5382_) == 0 {
                    v_a_5383_ = crate::leanh::lean_ctor_get(v___x_5382_, 0);
                    crate::leanh::lean_inc(v_a_5383_);
                    crate::leanh::lean_dec_ref_known(v___x_5382_, 1);
                    v___x_5384_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v_b_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
                    if crate::leanh::lean_obj_tag(v___x_5384_) == 0 {
                        v_a_5385_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                        v_isSharedCheck_5393_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5384_)) as u8;
                        if v_isSharedCheck_5393_ == 0 {
                            v___x_5387_ = v___x_5384_;
                            v_isShared_5388_ = v_isSharedCheck_5393_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5385_);
                            crate::leanh::lean_dec(v___x_5384_);
                            v___x_5387_ = crate::leanh::lean_box(0);
                            v_isShared_5388_ = v_isSharedCheck_5393_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5383_);
                        return v___x_5384_;
                    }
                } else {
                    return v___x_5382_;
                }
            }
            2 => {
                v___x_5389_ = lean_nat_add(v_a_5383_, v_a_5385_);
                crate::leanh::lean_dec(v_a_5385_);
                crate::leanh::lean_dec(v_a_5383_);
                if v_isShared_5388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5387_, 0, v___x_5389_);
                    v___x_5391_ = v___x_5387_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
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
                crate::leanh::lean_dec(v_a_5405_);
                crate::leanh::lean_dec(v_a_5403_);
                if v_isShared_5408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5407_, 0, v___x_5409_);
                    v___x_5411_ = v___x_5407_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5409_);
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
                crate::leanh::lean_dec_ref(v___x_5415_);
                if crate::leanh::lean_obj_tag(v___x_5418_) == 0 {
                    v_a_5419_ = crate::leanh::lean_ctor_get(v___x_5418_, 0);
                    crate::leanh::lean_inc(v_a_5419_);
                    crate::leanh::lean_dec_ref_known(v___x_5418_, 1);
                    v___x_5420_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5368_, v___x_5416_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
                    crate::leanh::lean_dec_ref(v___x_5416_);
                    if crate::leanh::lean_obj_tag(v___x_5420_) == 0 {
                        v_a_5421_ = crate::leanh::lean_ctor_get(v___x_5420_, 0);
                        v_isSharedCheck_5429_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5420_)) as u8;
                        if v_isSharedCheck_5429_ == 0 {
                            v___x_5423_ = v___x_5420_;
                            v_isShared_5424_ = v_isSharedCheck_5429_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5421_);
                            crate::leanh::lean_dec(v___x_5420_);
                            v___x_5423_ = crate::leanh::lean_box(0);
                            v_isShared_5424_ = v_isSharedCheck_5429_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5419_);
                        return v___x_5420_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5416_);
                    return v___x_5418_;
                }
            }
            7 => {
                v___x_5425_ = lean_nat_add(v_a_5419_, v_a_5421_);
                crate::leanh::lean_dec(v_a_5421_);
                crate::leanh::lean_dec(v_a_5419_);
                if v_isShared_5424_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5423_, 0, v___x_5425_);
                    v___x_5427_ = v___x_5423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5425_);
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
                    crate::leanh::lean_dec_ref(v_r_5431_);
                    state = 6;
                    continue;
                } else {
                    v___x_5434_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_5368_, v_r_5431_);
                    crate::leanh::lean_dec_ref(v_r_5431_);
                    if v___x_5434_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5416_);
                        crate::leanh::lean_dec_ref(v___x_5415_);
                        v___x_5435_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5436_, 0, v___x_5435_);
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
                    crate::leanh::lean_dec_ref(v_l_5430_);
                    state = 10;
                    continue;
                } else {
                    v___x_5442_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go_spec__0(v_xs_5368_, v_l_5430_);
                    crate::leanh::lean_dec_ref(v_l_5430_);
                    if v___x_5442_ == 0 {
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_r_5431_);
                        crate::leanh::lean_dec_ref(v___x_5416_);
                        crate::leanh::lean_dec_ref(v___x_5415_);
                        v___x_5443_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5444_, 0, v___x_5443_);
                        return v___x_5444_;
                    }
                }
            }
            12 => {
                v___x_5463_ = lean_nat_add(v_a_5455_, v_a_5457_);
                crate::leanh::lean_dec(v_a_5457_);
                crate::leanh::lean_dec(v_a_5455_);
                v___x_5464_ = lean_nat_add(v___x_5463_, v_a_5459_);
                crate::leanh::lean_dec(v_a_5459_);
                crate::leanh::lean_dec(v___x_5463_);
                if v_isShared_5462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5461_, 0, v___x_5464_);
                    v___x_5466_ = v___x_5461_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
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
    mut v_xs_5475_: *mut crate::leanh::LeanObject,
    mut v_e_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
    mut v_a_5478_: *mut crate::leanh::LeanObject,
    mut v_a_5479_: *mut crate::leanh::LeanObject,
    mut v_a_5480_: *mut crate::leanh::LeanObject,
    mut v_a_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5475_, v_e_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_);
    crate::leanh::lean_dec(v_a_5480_);
    crate::leanh::lean_dec_ref(v_a_5479_);
    crate::leanh::lean_dec(v_a_5478_);
    crate::leanh::lean_dec_ref(v_a_5477_);
    crate::leanh::lean_dec_ref(v_e_5476_);
    crate::leanh::lean_dec_ref(v_xs_5475_);
    return v_res_5482_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(
    mut v_xs_5483_: *mut crate::leanh::LeanObject,
    mut v_e_5484_: *mut crate::leanh::LeanObject,
    mut v_a_5485_: *mut crate::leanh::LeanObject,
    mut v_a_5486_: *mut crate::leanh::LeanObject,
    mut v_a_5487_: *mut crate::leanh::LeanObject,
    mut v_a_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5483_, v_e_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_);
    return v___x_5490_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars___boxed(
    mut v_xs_5491_: *mut crate::leanh::LeanObject,
    mut v_e_5492_: *mut crate::leanh::LeanObject,
    mut v_a_5493_: *mut crate::leanh::LeanObject,
    mut v_a_5494_: *mut crate::leanh::LeanObject,
    mut v_a_5495_: *mut crate::leanh::LeanObject,
    mut v_a_5496_: *mut crate::leanh::LeanObject,
    mut v_a_5497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5498_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars(v_xs_5491_, v_e_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_);
    crate::leanh::lean_dec(v_a_5496_);
    crate::leanh::lean_dec_ref(v_a_5495_);
    crate::leanh::lean_dec(v_a_5494_);
    crate::leanh::lean_dec_ref(v_a_5493_);
    crate::leanh::lean_dec_ref(v_e_5492_);
    crate::leanh::lean_dec_ref(v_xs_5491_);
    return v_res_5498_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = l_Lean_Meta_simpGlobalConfig;
    v_config_5500_ = crate::leanh::lean_ctor_get(v___x_5499_, 0);
    v_foApprox_5501_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 0 as u32);
    v_ctxApprox_5502_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 1 as u32);
    v_quasiPatternApprox_5503_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 2 as u32);
    v_constApprox_5504_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 3 as u32);
    v_isDefEqStuckEx_5505_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 4 as u32);
    v_unificationHints_5506_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 5 as u32);
    v_proofIrrelevance_5507_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 6 as u32);
    v_assignSyntheticOpaque_5508_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 7 as u32);
    v_offsetCnstrs_5509_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 8 as u32);
    v_transparency_5510_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 9 as u32);
    v_etaStruct_5511_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 10 as u32);
    v_univApprox_5512_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 11 as u32);
    v_zetaUnused_5513_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 17 as u32);
    v_zetaHave_5514_ = crate::leanh::lean_ctor_get_uint8(v_config_5500_, 18 as u32);
    v___x_5515_ = 1;
    v___x_5516_ = 2;
    v___x_5517_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 0 as u32, v_foApprox_5501_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 1 as u32, v_ctxApprox_5502_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 2 as u32, v_quasiPatternApprox_5503_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 3 as u32, v_constApprox_5504_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 4 as u32, v_isDefEqStuckEx_5505_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 5 as u32, v_unificationHints_5506_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 6 as u32, v_proofIrrelevance_5507_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 7 as u32, v_assignSyntheticOpaque_5508_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 8 as u32, v_offsetCnstrs_5509_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 9 as u32, v_transparency_5510_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 10 as u32, v_etaStruct_5511_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 11 as u32, v_univApprox_5512_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 12 as u32, v___x_5515_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 13 as u32, v___x_5515_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 14 as u32, v___x_5516_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 15 as u32, v___x_5515_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 16 as u32, v___x_5515_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 17 as u32, v_zetaUnused_5513_);
    crate::leanh::lean_ctor_set_uint8(v___x_5517_, 18 as u32, v_zetaHave_5514_);
    v___x_5518_ = l_Lean_Meta_Config_toConfigWithKey(v___x_5517_);
    return v___x_5518_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(
    mut v_k_5519_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5520_: u8,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
    mut v___y_5522_: *mut crate::leanh::LeanObject,
    mut v___y_5523_: *mut crate::leanh::LeanObject,
    mut v___y_5524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5530_: u8 = 0;
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5534_: u8 = 0;
    let mut v_a_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_5520_,
                    v_k_5519_,
                    v___y_5521_,
                    v___y_5522_,
                    v___y_5523_,
                    v___y_5524_,
                );
                if crate::leanh::lean_obj_tag(v___x_5526_) == 0 {
                    v_a_5527_ = crate::leanh::lean_ctor_get(v___x_5526_, 0);
                    v_isSharedCheck_5534_ = (!crate::leanh::lean_is_exclusive(v___x_5526_)) as u8;
                    if v_isSharedCheck_5534_ == 0 {
                        v___x_5529_ = v___x_5526_;
                        v_isShared_5530_ = v_isSharedCheck_5534_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5527_);
                        crate::leanh::lean_dec(v___x_5526_);
                        v___x_5529_ = crate::leanh::lean_box(0);
                        v_isShared_5530_ = v_isSharedCheck_5534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5535_ = crate::leanh::lean_ctor_get(v___x_5526_, 0);
                    v_isSharedCheck_5542_ = (!crate::leanh::lean_is_exclusive(v___x_5526_)) as u8;
                    if v_isSharedCheck_5542_ == 0 {
                        v___x_5537_ = v___x_5526_;
                        v_isShared_5538_ = v_isSharedCheck_5542_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5535_);
                        crate::leanh::lean_dec(v___x_5526_);
                        v___x_5537_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
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
                    v_reuseFailAlloc_5541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
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
    mut v_k_5543_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_5550_: u8 = 0;
    let mut v_res_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_5550_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_5544_) as u8);
    v_res_5551_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_5543_, v_allowLevelAssignments_boxed_5550_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_);
    crate::leanh::lean_dec(v___y_5548_);
    crate::leanh::lean_dec_ref(v___y_5547_);
    crate::leanh::lean_dec(v___y_5546_);
    crate::leanh::lean_dec_ref(v___y_5545_);
    return v_res_5551_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(
    mut v_00_u03b1_5552_: *mut crate::leanh::LeanObject,
    mut v_k_5553_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5554_: u8,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5560_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v_k_5553_, v_allowLevelAssignments_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
    return v___x_5560_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___boxed(
    mut v_00_u03b1_5561_: *mut crate::leanh::LeanObject,
    mut v_k_5562_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5563_: *mut crate::leanh::LeanObject,
    mut v___y_5564_: *mut crate::leanh::LeanObject,
    mut v___y_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_5569_: u8 = 0;
    let mut v_res_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_5569_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_5563_) as u8);
    v_res_5570_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1(v_00_u03b1_5561_, v_k_5562_, v_allowLevelAssignments_boxed_5569_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_);
    crate::leanh::lean_dec(v___y_5567_);
    crate::leanh::lean_dec_ref(v___y_5566_);
    crate::leanh::lean_dec(v___y_5565_);
    crate::leanh::lean_dec_ref(v___y_5564_);
    return v_res_5570_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(
    mut v___x_5571_: *mut crate::leanh::LeanObject,
    mut v___x_5572_: *mut crate::leanh::LeanObject,
    mut v_fst_5573_: *mut crate::leanh::LeanObject,
    mut v___x_5574_: *mut crate::leanh::LeanObject,
    mut v_expr_5575_: *mut crate::leanh::LeanObject,
    mut v_____r_5576_: *mut crate::leanh::LeanObject,
    mut v_lastSuccess_5577_: *mut crate::leanh::LeanObject,
    mut v_boundAssignments_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5592_: u8 = 0;
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut v_a_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5584_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5585_ = lean_nat_sub(v___x_5571_, v___x_5584_);
                v___x_5586_ = lean_nat_sub(v___x_5585_, v___x_5572_);
                crate::leanh::lean_dec(v___x_5585_);
                v___x_5587_ = l_Lean_Expr_getRevArg_x21(v_fst_5573_, v___x_5586_);
                v___x_5588_ = l_Lean_Meta_whnfR(
                    v___x_5587_,
                    v___y_5579_,
                    v___y_5580_,
                    v___y_5581_,
                    v___y_5582_,
                );
                if crate::leanh::lean_obj_tag(v___x_5588_) == 0 {
                    v_a_5589_ = crate::leanh::lean_ctor_get(v___x_5588_, 0);
                    v_isSharedCheck_5601_ = (!crate::leanh::lean_is_exclusive(v___x_5588_)) as u8;
                    if v_isSharedCheck_5601_ == 0 {
                        v___x_5591_ = v___x_5588_;
                        v_isShared_5592_ = v_isSharedCheck_5601_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5589_);
                        crate::leanh::lean_dec(v___x_5588_);
                        v___x_5591_ = crate::leanh::lean_box(0);
                        v_isShared_5592_ = v_isSharedCheck_5601_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_boundAssignments_5578_);
                    crate::leanh::lean_dec(v_lastSuccess_5577_);
                    crate::leanh::lean_dec_ref(v_expr_5575_);
                    crate::leanh::lean_dec(v___x_5574_);
                    v_a_5602_ = crate::leanh::lean_ctor_get(v___x_5588_, 0);
                    v_isSharedCheck_5609_ = (!crate::leanh::lean_is_exclusive(v___x_5588_)) as u8;
                    if v_isSharedCheck_5609_ == 0 {
                        v___x_5604_ = v___x_5588_;
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5602_);
                        crate::leanh::lean_dec(v___x_5588_);
                        v___x_5604_ = crate::leanh::lean_box(0);
                        v_isShared_5605_ = v_isSharedCheck_5609_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5593_, 0, v_lastSuccess_5577_);
                crate::leanh::lean_ctor_set(v___x_5593_, 1, v_boundAssignments_5578_);
                v___x_5594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5594_, 0, v___x_5574_);
                crate::leanh::lean_ctor_set(v___x_5594_, 1, v___x_5593_);
                v___x_5595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5595_, 0, v_expr_5575_);
                crate::leanh::lean_ctor_set(v___x_5595_, 1, v___x_5594_);
                v___x_5596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5596_, 0, v_a_5589_);
                crate::leanh::lean_ctor_set(v___x_5596_, 1, v___x_5595_);
                v___x_5597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5597_, 0, v___x_5596_);
                if v_isShared_5592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5591_, 0, v___x_5597_);
                    v___x_5599_ = v___x_5591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5597_);
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
                    v_reuseFailAlloc_5608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
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
    mut v___x_5610_: *mut crate::leanh::LeanObject,
    mut v___x_5611_: *mut crate::leanh::LeanObject,
    mut v_fst_5612_: *mut crate::leanh::LeanObject,
    mut v___x_5613_: *mut crate::leanh::LeanObject,
    mut v_expr_5614_: *mut crate::leanh::LeanObject,
    mut v_____r_5615_: *mut crate::leanh::LeanObject,
    mut v_lastSuccess_5616_: *mut crate::leanh::LeanObject,
    mut v_boundAssignments_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5623_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_5610_, v___x_5611_, v_fst_5612_, v___x_5613_, v_expr_5614_, v_____r_5615_, v_lastSuccess_5616_, v_boundAssignments_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    crate::leanh::lean_dec(v___y_5621_);
    crate::leanh::lean_dec_ref(v___y_5620_);
    crate::leanh::lean_dec(v___y_5619_);
    crate::leanh::lean_dec_ref(v___y_5618_);
    crate::leanh::lean_dec(v_fst_5612_);
    crate::leanh::lean_dec(v___x_5611_);
    crate::leanh::lean_dec(v___x_5610_);
    return v_res_5623_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5631_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5631_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5632_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__4);
    v___x_5633_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5633_, 0, v___x_5632_);
    return v___x_5633_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5634_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5635_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
    v___x_5636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5636_, 0, v___x_5635_);
    crate::leanh::lean_ctor_set(v___x_5636_, 1, v___x_5634_);
    return v___x_5636_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5637_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5638_ = lean_mk_empty_array_with_capacity(v___x_5637_);
    v___x_5639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5639_, 0, v___x_5638_);
    return v___x_5639_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5640_: usize = 0;
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5640_ = 5usize;
    v___x_5641_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5642_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5643_ = lean_mk_empty_array_with_capacity(v___x_5642_);
    v___x_5644_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__7);
    v___x_5645_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5645_, 0, v___x_5644_);
    crate::leanh::lean_ctor_set(v___x_5645_, 1, v___x_5643_);
    crate::leanh::lean_ctor_set(v___x_5645_, 2, v___x_5641_);
    crate::leanh::lean_ctor_set(v___x_5645_, 3, v___x_5641_);
    crate::leanh::lean_ctor_set_usize(v___x_5645_, 4, v___x_5640_);
    return v___x_5645_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5646_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__8);
    v___x_5647_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__5);
    v___x_5648_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5648_, 0, v___x_5647_);
    crate::leanh::lean_ctor_set(v___x_5648_, 1, v___x_5647_);
    crate::leanh::lean_ctor_set(v___x_5648_, 2, v___x_5647_);
    crate::leanh::lean_ctor_set(v___x_5648_, 3, v___x_5646_);
    return v___x_5648_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__9);
    v___x_5650_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__6);
    v___x_5651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5651_, 0, v___x_5650_);
    crate::leanh::lean_ctor_set(v___x_5651_, 1, v___x_5649_);
    return v___x_5651_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(
    mut v_a_5652_: *mut crate::leanh::LeanObject,
    mut v_xs_5653_: *mut crate::leanh::LeanObject,
    mut v_a_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v_a_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v_a_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5676_: u8 = 0;
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut v_snd_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v_fst_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5691_: u8 = 0;
    let mut v_fst_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5695_: u8 = 0;
    let mut v_fst_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: u8 = 0;
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: u8 = 0;
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: u8 = 0;
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5751_: u8 = 0;
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5755_: u8 = 0;
    let mut v_a_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5763_: u8 = 0;
    let mut v_a_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5767_: u8 = 0;
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5771_: u8 = 0;
    let mut v_isSharedCheck_5772_: u8 = 0;
    let mut v_isSharedCheck_5773_: u8 = 0;
    let mut v_unused_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v_unused_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5777_: u8 = 0;
    let mut v_unused_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_5681_ = crate::leanh::lean_ctor_get(v_a_5654_, 1);
                crate::leanh::lean_inc(v_snd_5681_);
                v_snd_5682_ = crate::leanh::lean_ctor_get(v_snd_5681_, 1);
                crate::leanh::lean_inc(v_snd_5682_);
                v_snd_5683_ = crate::leanh::lean_ctor_get(v_snd_5682_, 1);
                crate::leanh::lean_inc(v_snd_5683_);
                v_fst_5684_ = crate::leanh::lean_ctor_get(v_a_5654_, 0);
                v_isSharedCheck_5777_ = (!crate::leanh::lean_is_exclusive(v_a_5654_)) as u8;
                if v_isSharedCheck_5777_ == 0 {
                    v_unused_5778_ = crate::leanh::lean_ctor_get(v_a_5654_, 1);
                    crate::leanh::lean_dec(v_unused_5778_);
                    v___x_5686_ = v_a_5654_;
                    v_isShared_5687_ = v_isSharedCheck_5777_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5684_);
                    crate::leanh::lean_dec(v_a_5654_);
                    v___x_5686_ = crate::leanh::lean_box(0);
                    v_isShared_5687_ = v_isSharedCheck_5777_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5661_) == 0 {
                    v_a_5662_ = crate::leanh::lean_ctor_get(v___y_5661_, 0);
                    v_isSharedCheck_5672_ = (!crate::leanh::lean_is_exclusive(v___y_5661_)) as u8;
                    if v_isSharedCheck_5672_ == 0 {
                        v___x_5664_ = v___y_5661_;
                        v_isShared_5665_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5662_);
                        crate::leanh::lean_dec(v___y_5661_);
                        v___x_5664_ = crate::leanh::lean_box(0);
                        v_isShared_5665_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5652_);
                    v_a_5673_ = crate::leanh::lean_ctor_get(v___y_5661_, 0);
                    v_isSharedCheck_5680_ = (!crate::leanh::lean_is_exclusive(v___y_5661_)) as u8;
                    if v_isSharedCheck_5680_ == 0 {
                        v___x_5675_ = v___y_5661_;
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5673_);
                        crate::leanh::lean_dec(v___y_5661_);
                        v___x_5675_ = crate::leanh::lean_box(0);
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5662_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_5652_);
                    v_a_5666_ = crate::leanh::lean_ctor_get(v_a_5662_, 0);
                    crate::leanh::lean_inc(v_a_5666_);
                    crate::leanh::lean_dec_ref_known(v_a_5662_, 1);
                    if v_isShared_5665_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5664_, 0, v_a_5666_);
                        v___x_5668_ = v___x_5664_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5666_);
                        v___x_5668_ = v_reuseFailAlloc_5669_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5664_);
                    v_a_5670_ = crate::leanh::lean_ctor_get(v_a_5662_, 0);
                    crate::leanh::lean_inc(v_a_5670_);
                    crate::leanh::lean_dec_ref_known(v_a_5662_, 1);
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
                    v_reuseFailAlloc_5679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5673_);
                    v___x_5678_ = v_reuseFailAlloc_5679_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5678_;
            }
            6 => {
                v_fst_5688_ = crate::leanh::lean_ctor_get(v_snd_5681_, 0);
                v_isSharedCheck_5775_ = (!crate::leanh::lean_is_exclusive(v_snd_5681_)) as u8;
                if v_isSharedCheck_5775_ == 0 {
                    v_unused_5776_ = crate::leanh::lean_ctor_get(v_snd_5681_, 1);
                    crate::leanh::lean_dec(v_unused_5776_);
                    v___x_5690_ = v_snd_5681_;
                    v_isShared_5691_ = v_isSharedCheck_5775_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5688_);
                    crate::leanh::lean_dec(v_snd_5681_);
                    v___x_5690_ = crate::leanh::lean_box(0);
                    v_isShared_5691_ = v_isSharedCheck_5775_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_5692_ = crate::leanh::lean_ctor_get(v_snd_5682_, 0);
                v_isSharedCheck_5773_ = (!crate::leanh::lean_is_exclusive(v_snd_5682_)) as u8;
                if v_isSharedCheck_5773_ == 0 {
                    v_unused_5774_ = crate::leanh::lean_ctor_get(v_snd_5682_, 1);
                    crate::leanh::lean_dec(v_unused_5774_);
                    v___x_5694_ = v_snd_5682_;
                    v_isShared_5695_ = v_isSharedCheck_5773_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5692_);
                    crate::leanh::lean_dec(v_snd_5682_);
                    v___x_5694_ = crate::leanh::lean_box(0);
                    v_isShared_5695_ = v_isSharedCheck_5773_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_5696_ = crate::leanh::lean_ctor_get(v_snd_5683_, 0);
                v_snd_5697_ = crate::leanh::lean_ctor_get(v_snd_5683_, 1);
                v_isSharedCheck_5772_ = (!crate::leanh::lean_is_exclusive(v_snd_5683_)) as u8;
                if v_isSharedCheck_5772_ == 0 {
                    v___x_5699_ = v_snd_5683_;
                    v_isShared_5700_ = v_isSharedCheck_5772_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5697_);
                    crate::leanh::lean_inc(v_fst_5696_);
                    crate::leanh::lean_dec(v_snd_5683_);
                    v___x_5699_ = crate::leanh::lean_box(0);
                    v_isShared_5700_ = v_isSharedCheck_5772_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5701_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__2;
                v___x_5702_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5703_ = l_Lean_Expr_isAppOfArity(v_fst_5684_, v___x_5701_, v___x_5702_);
                if v___x_5703_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_5652_);
                    if v_isShared_5700_ == 0 {
                        v___x_5705_ = v___x_5699_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_fst_5696_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_snd_5697_);
                        v___x_5705_ = v_reuseFailAlloc_5716_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5699_);
                    crate::leanh::lean_del_object(v___x_5694_);
                    crate::leanh::lean_del_object(v___x_5690_);
                    crate::leanh::lean_del_object(v___x_5686_);
                    v___x_5717_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5718_ = l_Lean_Expr_getAppNumArgs(v_fst_5684_);
                    v___x_5719_ = lean_nat_sub(v___x_5718_, v___x_5717_);
                    v___x_5720_ = lean_nat_sub(v___x_5719_, v___x_5717_);
                    crate::leanh::lean_dec(v___x_5719_);
                    v___x_5721_ = l_Lean_Expr_getRevArg_x21(v_fst_5684_, v___x_5720_);
                    v___x_5722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5722_, 0, v___x_5721_);
                    v___x_5723_ = 0;
                    v___x_5724_ = crate::leanh::lean_box(0);
                    v___x_5725_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_5722_,
                        v___x_5723_,
                        v___x_5724_,
                        v___y_5655_,
                        v___y_5656_,
                        v___y_5657_,
                        v___y_5658_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5725_) == 0 {
                        v_a_5726_ = crate::leanh::lean_ctor_get(v___x_5725_, 0);
                        crate::leanh::lean_inc(v_a_5726_);
                        crate::leanh::lean_dec_ref_known(v___x_5725_, 1);
                        v___x_5727_ = lean_mk_empty_array_with_capacity(v___x_5717_);
                        v___x_5728_ = lean_array_push(v___x_5727_, v_a_5726_);
                        v___x_5729_ = l_Lean_Expr_beta(v_fst_5688_, v___x_5728_);
                        v___x_5730_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__3;
                        v___x_5731_ = crate::leanh::lean_box(0);
                        v___x_5732_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___closed__10);
                        crate::leanh::lean_inc_ref(v_a_5652_);
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
                        if crate::leanh::lean_obj_tag(v___x_5733_) == 0 {
                            v_a_5734_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                            crate::leanh::lean_inc(v_a_5734_);
                            crate::leanh::lean_dec_ref_known(v___x_5733_, 1);
                            v_fst_5735_ = crate::leanh::lean_ctor_get(v_a_5734_, 0);
                            crate::leanh::lean_inc(v_fst_5735_);
                            crate::leanh::lean_dec(v_a_5734_);
                            v_expr_5736_ = crate::leanh::lean_ctor_get(v_fst_5735_, 0);
                            crate::leanh::lean_inc_ref(v_expr_5736_);
                            crate::leanh::lean_dec(v_fst_5735_);
                            v___x_5737_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5653_, v_expr_5736_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
                            if crate::leanh::lean_obj_tag(v___x_5737_) == 0 {
                                v_a_5738_ = crate::leanh::lean_ctor_get(v___x_5737_, 0);
                                crate::leanh::lean_inc(v_a_5738_);
                                crate::leanh::lean_dec_ref_known(v___x_5737_, 1);
                                v___x_5739_ = lean_nat_add(v_fst_5692_, v___x_5717_);
                                crate::leanh::lean_dec(v_fst_5692_);
                                v___x_5743_ = lean_nat_dec_lt(v_a_5738_, v_snd_5697_);
                                if v___x_5743_ == 0 {
                                    v___x_5744_ = l_Lean_Expr_getAppFn_x27(v_expr_5736_);
                                    v___x_5745_ = l_Lean_Expr_isMVar(v___x_5744_);
                                    crate::leanh::lean_dec_ref(v___x_5744_);
                                    if v___x_5745_ == 0 {
                                        crate::leanh::lean_dec(v_a_5738_);
                                        v___x_5746_ = crate::leanh::lean_box(0);
                                        v___x_5747_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_5718_, v___x_5717_, v_fst_5684_, v___x_5739_, v_expr_5736_, v___x_5746_, v_fst_5696_, v_snd_5697_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
                                        crate::leanh::lean_dec(v_fst_5684_);
                                        crate::leanh::lean_dec(v___x_5718_);
                                        v___y_5661_ = v___x_5747_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_snd_5697_);
                                        crate::leanh::lean_dec(v_fst_5696_);
                                        state = 14;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_snd_5697_);
                                    crate::leanh::lean_dec(v_fst_5696_);
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_expr_5736_);
                                crate::leanh::lean_dec(v___x_5718_);
                                crate::leanh::lean_dec(v_snd_5697_);
                                crate::leanh::lean_dec(v_fst_5696_);
                                crate::leanh::lean_dec(v_fst_5692_);
                                crate::leanh::lean_dec(v_fst_5684_);
                                crate::leanh::lean_dec_ref(v_a_5652_);
                                v_a_5748_ = crate::leanh::lean_ctor_get(v___x_5737_, 0);
                                v_isSharedCheck_5755_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5737_)) as u8;
                                if v_isSharedCheck_5755_ == 0 {
                                    v___x_5750_ = v___x_5737_;
                                    v_isShared_5751_ = v_isSharedCheck_5755_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5748_);
                                    crate::leanh::lean_dec(v___x_5737_);
                                    v___x_5750_ = crate::leanh::lean_box(0);
                                    v_isShared_5751_ = v_isSharedCheck_5755_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5718_);
                            crate::leanh::lean_dec(v_snd_5697_);
                            crate::leanh::lean_dec(v_fst_5696_);
                            crate::leanh::lean_dec(v_fst_5692_);
                            crate::leanh::lean_dec(v_fst_5684_);
                            crate::leanh::lean_dec_ref(v_a_5652_);
                            v_a_5756_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                            v_isSharedCheck_5763_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5733_)) as u8;
                            if v_isSharedCheck_5763_ == 0 {
                                v___x_5758_ = v___x_5733_;
                                v_isShared_5759_ = v_isSharedCheck_5763_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5756_);
                                crate::leanh::lean_dec(v___x_5733_);
                                v___x_5758_ = crate::leanh::lean_box(0);
                                v_isShared_5759_ = v_isSharedCheck_5763_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5718_);
                        crate::leanh::lean_dec(v_snd_5697_);
                        crate::leanh::lean_dec(v_fst_5696_);
                        crate::leanh::lean_dec(v_fst_5692_);
                        crate::leanh::lean_dec(v_fst_5688_);
                        crate::leanh::lean_dec(v_fst_5684_);
                        crate::leanh::lean_dec_ref(v_a_5652_);
                        v_a_5764_ = crate::leanh::lean_ctor_get(v___x_5725_, 0);
                        v_isSharedCheck_5771_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5725_)) as u8;
                        if v_isSharedCheck_5771_ == 0 {
                            v___x_5766_ = v___x_5725_;
                            v_isShared_5767_ = v_isSharedCheck_5771_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5764_);
                            crate::leanh::lean_dec(v___x_5725_);
                            v___x_5766_ = crate::leanh::lean_box(0);
                            v_isShared_5767_ = v_isSharedCheck_5771_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_5695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5694_, 1, v___x_5705_);
                    v___x_5707_ = v___x_5694_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_fst_5692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 1, v___x_5705_);
                    v___x_5707_ = v_reuseFailAlloc_5715_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5690_, 1, v___x_5707_);
                    v___x_5709_ = v___x_5690_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_fst_5688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 1, v___x_5707_);
                    v___x_5709_ = v_reuseFailAlloc_5714_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_5687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5686_, 1, v___x_5709_);
                    v___x_5711_ = v___x_5686_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 0, v_fst_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5709_);
                    v___x_5711_ = v_reuseFailAlloc_5713_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5712_, 0, v___x_5711_);
                return v___x_5712_;
            }
            14 => {
                v___x_5741_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_5739_);
                v___x_5742_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg___lam__0(v___x_5718_, v___x_5717_, v_fst_5684_, v___x_5739_, v_expr_5736_, v___x_5741_, v___x_5739_, v_a_5738_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
                crate::leanh::lean_dec(v_fst_5684_);
                crate::leanh::lean_dec(v___x_5718_);
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
                    v_reuseFailAlloc_5754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
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
                    v_reuseFailAlloc_5762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_a_5756_);
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
                    v_reuseFailAlloc_5770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_a_5764_);
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
    mut v_a_5779_: *mut crate::leanh::LeanObject,
    mut v_xs_5780_: *mut crate::leanh::LeanObject,
    mut v_a_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
    mut v___y_5786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5787_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_5779_, v_xs_5780_, v_a_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
    crate::leanh::lean_dec(v___y_5785_);
    crate::leanh::lean_dec_ref(v___y_5784_);
    crate::leanh::lean_dec(v___y_5783_);
    crate::leanh::lean_dec_ref(v___y_5782_);
    crate::leanh::lean_dec_ref(v_xs_5780_);
    return v_res_5787_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0(
    mut v___x_5788_: *mut crate::leanh::LeanObject,
    mut v___x_5789_: u8,
    mut v_00_u03c3s_5790_: *mut crate::leanh::LeanObject,
    mut v_xs_5791_: *mut crate::leanh::LeanObject,
    mut v_e_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5801_: u8 = 0;
    let mut v_trackZetaDelta_5802_: u8 = 0;
    let mut v_zetaDeltaSet_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5809_: u8 = 0;
    let mut v_inTypeClassResolution_5810_: u8 = 0;
    let mut v_cacheInferType_5811_: u8 = 0;
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5814_: u8 = 0;
    let mut v___x_5815_: u64 = 0;
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v_snd_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_a_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5847_: u8 = 0;
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5851_: u8 = 0;
    let mut v_a_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5855_: u8 = 0;
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5859_: u8 = 0;
    let mut v_a_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5867_: u8 = 0;
    let mut v_reuseFailAlloc_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_unused_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5872_: u8 = 0;
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_5789_ == 0 {
                    v_config_5798_ = crate::leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5872_ = (!crate::leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5872_ == 0 {
                        v___x_5800_ = v___x_5788_;
                        v_isShared_5801_ = v_isSharedCheck_5872_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_config_5798_);
                        crate::leanh::lean_dec(v___x_5788_);
                        v___x_5800_ = crate::leanh::lean_box(0);
                        v_isShared_5801_ = v_isSharedCheck_5872_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5793_);
                    crate::leanh::lean_dec_ref(v_e_5792_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5790_);
                    crate::leanh::lean_dec_ref(v___x_5788_);
                    v___x_5873_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5874_, 0, v___x_5873_);
                    return v___x_5874_;
                }
            }
            1 => {
                v_trackZetaDelta_5802_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5803_ = crate::leanh::lean_ctor_get(v___y_5793_, 1);
                v_lctx_5804_ = crate::leanh::lean_ctor_get(v___y_5793_, 2);
                v_localInstances_5805_ = crate::leanh::lean_ctor_get(v___y_5793_, 3);
                v_defEqCtx_x3f_5806_ = crate::leanh::lean_ctor_get(v___y_5793_, 4);
                v_synthPendingDepth_5807_ = crate::leanh::lean_ctor_get(v___y_5793_, 5);
                v_canUnfold_x3f_5808_ = crate::leanh::lean_ctor_get(v___y_5793_, 6);
                v_univApprox_5809_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5810_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5811_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5793_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v_isSharedCheck_5870_ = (!crate::leanh::lean_is_exclusive(v___y_5793_)) as u8;
                if v_isSharedCheck_5870_ == 0 {
                    v_unused_5871_ = crate::leanh::lean_ctor_get(v___y_5793_, 0);
                    crate::leanh::lean_dec(v_unused_5871_);
                    v___x_5813_ = v___y_5793_;
                    v_isShared_5814_ = v_isSharedCheck_5870_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canUnfold_x3f_5808_);
                    crate::leanh::lean_inc(v_synthPendingDepth_5807_);
                    crate::leanh::lean_inc(v_defEqCtx_x3f_5806_);
                    crate::leanh::lean_inc(v_localInstances_5805_);
                    crate::leanh::lean_inc(v_lctx_5804_);
                    crate::leanh::lean_inc(v_zetaDeltaSet_5803_);
                    crate::leanh::lean_dec(v___y_5793_);
                    v___x_5813_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5869_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_config_5798_);
                    v___x_5817_ = v_reuseFailAlloc_5869_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint64(
                    v___x_5817_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5815_,
                );
                if v_isShared_5814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5813_, 0, v___x_5817_);
                    v___x_5819_ = v___x_5813_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5868_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_zetaDeltaSet_5803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_lctx_5804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 3, v_localInstances_5805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_defEqCtx_x3f_5806_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5868_,
                        5,
                        v_synthPendingDepth_5807_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 6, v_canUnfold_x3f_5808_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_5802_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_5809_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_5810_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5868_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
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
                if crate::leanh::lean_obj_tag(v___x_5820_) == 0 {
                    v_a_5821_ = crate::leanh::lean_ctor_get(v___x_5820_, 0);
                    crate::leanh::lean_inc(v_a_5821_);
                    crate::leanh::lean_dec_ref_known(v___x_5820_, 1);
                    v___x_5822_ = l_Lean_Meta_whnfR(
                        v_00_u03c3s_5790_,
                        v___x_5819_,
                        v___y_5794_,
                        v___y_5795_,
                        v___y_5796_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5822_) == 0 {
                        v_a_5823_ = crate::leanh::lean_ctor_get(v___x_5822_, 0);
                        crate::leanh::lean_inc(v_a_5823_);
                        crate::leanh::lean_dec_ref_known(v___x_5822_, 1);
                        v___x_5824_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_countBVarDependentMVars_go(v_xs_5791_, v_e_5792_, v___x_5819_, v___y_5794_, v___y_5795_, v___y_5796_);
                        if crate::leanh::lean_obj_tag(v___x_5824_) == 0 {
                            v_a_5825_ = crate::leanh::lean_ctor_get(v___x_5824_, 0);
                            crate::leanh::lean_inc(v_a_5825_);
                            crate::leanh::lean_dec_ref_known(v___x_5824_, 1);
                            v___x_5826_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_5827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5827_, 0, v___x_5826_);
                            crate::leanh::lean_ctor_set(v___x_5827_, 1, v_a_5825_);
                            v___x_5828_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5828_, 0, v___x_5826_);
                            crate::leanh::lean_ctor_set(v___x_5828_, 1, v___x_5827_);
                            v___x_5829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5829_, 0, v_e_5792_);
                            crate::leanh::lean_ctor_set(v___x_5829_, 1, v___x_5828_);
                            v___x_5830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5830_, 0, v_a_5823_);
                            crate::leanh::lean_ctor_set(v___x_5830_, 1, v___x_5829_);
                            v___x_5831_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_5821_, v_xs_5791_, v___x_5830_, v___x_5819_, v___y_5794_, v___y_5795_, v___y_5796_);
                            crate::leanh::lean_dec_ref(v___x_5819_);
                            if crate::leanh::lean_obj_tag(v___x_5831_) == 0 {
                                v_a_5832_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                                v_isSharedCheck_5843_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5831_)) as u8;
                                if v_isSharedCheck_5843_ == 0 {
                                    v___x_5834_ = v___x_5831_;
                                    v_isShared_5835_ = v_isSharedCheck_5843_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5832_);
                                    crate::leanh::lean_dec(v___x_5831_);
                                    v___x_5834_ = crate::leanh::lean_box(0);
                                    v_isShared_5835_ = v_isSharedCheck_5843_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_5844_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                                v_isSharedCheck_5851_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5831_)) as u8;
                                if v_isSharedCheck_5851_ == 0 {
                                    v___x_5846_ = v___x_5831_;
                                    v_isShared_5847_ = v_isSharedCheck_5851_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5844_);
                                    crate::leanh::lean_dec(v___x_5831_);
                                    v___x_5846_ = crate::leanh::lean_box(0);
                                    v_isShared_5847_ = v_isSharedCheck_5851_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5823_);
                            crate::leanh::lean_dec(v_a_5821_);
                            crate::leanh::lean_dec_ref(v___x_5819_);
                            crate::leanh::lean_dec_ref(v_e_5792_);
                            return v___x_5824_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5821_);
                        crate::leanh::lean_dec_ref(v___x_5819_);
                        crate::leanh::lean_dec_ref(v_e_5792_);
                        v_a_5852_ = crate::leanh::lean_ctor_get(v___x_5822_, 0);
                        v_isSharedCheck_5859_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5822_)) as u8;
                        if v_isSharedCheck_5859_ == 0 {
                            v___x_5854_ = v___x_5822_;
                            v_isShared_5855_ = v_isSharedCheck_5859_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5852_);
                            crate::leanh::lean_dec(v___x_5822_);
                            v___x_5854_ = crate::leanh::lean_box(0);
                            v_isShared_5855_ = v_isSharedCheck_5859_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5819_);
                    crate::leanh::lean_dec_ref(v_e_5792_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_5790_);
                    v_a_5860_ = crate::leanh::lean_ctor_get(v___x_5820_, 0);
                    v_isSharedCheck_5867_ = (!crate::leanh::lean_is_exclusive(v___x_5820_)) as u8;
                    if v_isSharedCheck_5867_ == 0 {
                        v___x_5862_ = v___x_5820_;
                        v_isShared_5863_ = v_isSharedCheck_5867_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5860_);
                        crate::leanh::lean_dec(v___x_5820_);
                        v___x_5862_ = crate::leanh::lean_box(0);
                        v_isShared_5863_ = v_isSharedCheck_5867_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_5836_ = crate::leanh::lean_ctor_get(v_a_5832_, 1);
                crate::leanh::lean_inc(v_snd_5836_);
                crate::leanh::lean_dec(v_a_5832_);
                v_snd_5837_ = crate::leanh::lean_ctor_get(v_snd_5836_, 1);
                crate::leanh::lean_inc(v_snd_5837_);
                crate::leanh::lean_dec(v_snd_5836_);
                v_snd_5838_ = crate::leanh::lean_ctor_get(v_snd_5837_, 1);
                crate::leanh::lean_inc(v_snd_5838_);
                crate::leanh::lean_dec(v_snd_5837_);
                v_fst_5839_ = crate::leanh::lean_ctor_get(v_snd_5838_, 0);
                crate::leanh::lean_inc(v_fst_5839_);
                crate::leanh::lean_dec(v_snd_5838_);
                if v_isShared_5835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5834_, 0, v_fst_5839_);
                    v___x_5841_ = v___x_5834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_fst_5839_);
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
                    v_reuseFailAlloc_5850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
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
                    v_reuseFailAlloc_5858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
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
                    v_reuseFailAlloc_5866_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
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
    mut v___x_5875_: *mut crate::leanh::LeanObject,
    mut v___x_5876_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5877_: *mut crate::leanh::LeanObject,
    mut v_xs_5878_: *mut crate::leanh::LeanObject,
    mut v_e_5879_: *mut crate::leanh::LeanObject,
    mut v___y_5880_: *mut crate::leanh::LeanObject,
    mut v___y_5881_: *mut crate::leanh::LeanObject,
    mut v___y_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5010__boxed_5885_: u8 = 0;
    let mut v_res_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5010__boxed_5885_ = (crate::leanh::lean_unbox(v___x_5876_) as u8);
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
    crate::leanh::lean_dec(v___y_5883_);
    crate::leanh::lean_dec_ref(v___y_5882_);
    crate::leanh::lean_dec(v___y_5881_);
    crate::leanh::lean_dec_ref(v_xs_5878_);
    return v_res_5886_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
    mut v_xs_5887_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5888_: *mut crate::leanh::LeanObject,
    mut v_e_5889_: *mut crate::leanh::LeanObject,
    mut v_a_5890_: *mut crate::leanh::LeanObject,
    mut v_a_5891_: *mut crate::leanh::LeanObject,
    mut v_a_5892_: *mut crate::leanh::LeanObject,
    mut v_a_5893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: u8 = 0;
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: u8 = 0;
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5895_ = l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig;
    v___x_5896_ = lean_array_get_size(v_xs_5887_);
    v___x_5897_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5898_ = lean_nat_dec_eq(v___x_5896_, v___x_5897_);
    v___x_5899_ = crate::leanh::lean_box((v___x_5898_) as usize);
    v___f_5900_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5900_, 0, v___x_5895_);
    crate::leanh::lean_closure_set(v___f_5900_, 1, v___x_5899_);
    crate::leanh::lean_closure_set(v___f_5900_, 2, v_00_u03c3s_5888_);
    crate::leanh::lean_closure_set(v___f_5900_, 3, v_xs_5887_);
    crate::leanh::lean_closure_set(v___f_5900_, 4, v_e_5889_);
    v___x_5901_ = 0;
    v___x_5902_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__1___redArg(v___f_5900_, v___x_5901_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
    return v___x_5902_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred___boxed(
    mut v_xs_5903_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_5904_: *mut crate::leanh::LeanObject,
    mut v_e_5905_: *mut crate::leanh::LeanObject,
    mut v_a_5906_: *mut crate::leanh::LeanObject,
    mut v_a_5907_: *mut crate::leanh::LeanObject,
    mut v_a_5908_: *mut crate::leanh::LeanObject,
    mut v_a_5909_: *mut crate::leanh::LeanObject,
    mut v_a_5910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5911_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
        v_xs_5903_,
        v_00_u03c3s_5904_,
        v_e_5905_,
        v_a_5906_,
        v_a_5907_,
        v_a_5908_,
        v_a_5909_,
    );
    crate::leanh::lean_dec(v_a_5909_);
    crate::leanh::lean_dec_ref(v_a_5908_);
    crate::leanh::lean_dec(v_a_5907_);
    crate::leanh::lean_dec_ref(v_a_5906_);
    return v_res_5911_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(
    mut v_a_5912_: *mut crate::leanh::LeanObject,
    mut v_xs_5913_: *mut crate::leanh::LeanObject,
    mut v_inst_5914_: *mut crate::leanh::LeanObject,
    mut v_a_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
    mut v___y_5917_: *mut crate::leanh::LeanObject,
    mut v___y_5918_: *mut crate::leanh::LeanObject,
    mut v___y_5919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5921_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___redArg(v_a_5912_, v_xs_5913_, v_a_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
    return v___x_5921_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0___boxed(
    mut v_a_5922_: *mut crate::leanh::LeanObject,
    mut v_xs_5923_: *mut crate::leanh::LeanObject,
    mut v_inst_5924_: *mut crate::leanh::LeanObject,
    mut v_a_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5931_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred_spec__0(v_a_5922_, v_xs_5923_, v_inst_5924_, v_a_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
    crate::leanh::lean_dec(v___y_5929_);
    crate::leanh::lean_dec_ref(v___y_5928_);
    crate::leanh::lean_dec(v___y_5927_);
    crate::leanh::lean_dec_ref(v___y_5926_);
    crate::leanh::lean_dec_ref(v_xs_5923_);
    return v_res_5931_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5933_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__0;
    v___x_5934_ = l_Lean_stringToMessageData(v___x_5933_);
    return v___x_5934_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0(
    mut v_a_5948_: *mut crate::leanh::LeanObject,
    mut v___x_5949_: *mut crate::leanh::LeanObject,
    mut v___x_5950_: u8,
    mut v___x_5951_: *mut crate::leanh::LeanObject,
    mut v_proof_5952_: *mut crate::leanh::LeanObject,
    mut v_prio_5953_: *mut crate::leanh::LeanObject,
    mut v___y_5954_: *mut crate::leanh::LeanObject,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5961_: u8 = 0;
    let mut v_zetaDeltaSet_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5968_: u8 = 0;
    let mut v_inTypeClassResolution_5969_: u8 = 0;
    let mut v_cacheInferType_5970_: u8 = 0;
    let mut v___x_5971_: u64 = 0;
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5980_: u8 = 0;
    let mut v_snd_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: u8 = 0;
    let mut v_arg_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut v_arg_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: u8 = 0;
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: u8 = 0;
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: u8 = 0;
    let mut v_arg_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: u8 = 0;
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: u8 = 0;
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: u8 = 0;
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6037_: u8 = 0;
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6042_: u8 = 0;
    let mut v_a_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6046_: u8 = 0;
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6050_: u8 = 0;
    let mut v_a_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v_reuseFailAlloc_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6063_: u8 = 0;
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6067_: u8 = 0;
    let mut v_a_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6071_: u8 = 0;
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut v_isSharedCheck_6076_: u8 = 0;
    let mut v_unused_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6078_: u8 = 0;
    let mut v_a_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5959_ = l_Lean_Meta_simpGlobalConfig;
                v_config_5960_ = crate::leanh::lean_ctor_get(v___x_5959_, 0);
                v_trackZetaDelta_5961_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5962_ = crate::leanh::lean_ctor_get(v___y_5954_, 1);
                v_lctx_5963_ = crate::leanh::lean_ctor_get(v___y_5954_, 2);
                v_localInstances_5964_ = crate::leanh::lean_ctor_get(v___y_5954_, 3);
                v_defEqCtx_x3f_5965_ = crate::leanh::lean_ctor_get(v___y_5954_, 4);
                v_synthPendingDepth_5966_ = crate::leanh::lean_ctor_get(v___y_5954_, 5);
                v_canUnfold_x3f_5967_ = crate::leanh::lean_ctor_get(v___y_5954_, 6);
                v_univApprox_5968_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5969_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5970_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5954_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_5960_);
                crate::leanh::lean_inc_ref(v_config_5960_);
                v___x_5972_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_5972_, 0, v_config_5960_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_5972_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5971_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_5967_);
                crate::leanh::lean_inc(v_synthPendingDepth_5966_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_5965_);
                crate::leanh::lean_inc_ref(v_localInstances_5964_);
                crate::leanh::lean_inc_ref(v_lctx_5963_);
                crate::leanh::lean_inc(v_zetaDeltaSet_5962_);
                v___x_5973_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_5973_, 0, v___x_5972_);
                crate::leanh::lean_ctor_set(v___x_5973_, 1, v_zetaDeltaSet_5962_);
                crate::leanh::lean_ctor_set(v___x_5973_, 2, v_lctx_5963_);
                crate::leanh::lean_ctor_set(v___x_5973_, 3, v_localInstances_5964_);
                crate::leanh::lean_ctor_set(v___x_5973_, 4, v_defEqCtx_x3f_5965_);
                crate::leanh::lean_ctor_set(v___x_5973_, 5, v_synthPendingDepth_5966_);
                crate::leanh::lean_ctor_set(v___x_5973_, 6, v_canUnfold_x3f_5967_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5961_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5968_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5969_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5973_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
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
                crate::leanh::lean_dec_ref_known(v___x_5973_, 7);
                if crate::leanh::lean_obj_tag(v___x_5974_) == 0 {
                    v_a_5975_ = crate::leanh::lean_ctor_get(v___x_5974_, 0);
                    crate::leanh::lean_inc(v_a_5975_);
                    crate::leanh::lean_dec_ref_known(v___x_5974_, 1);
                    v_snd_5976_ = crate::leanh::lean_ctor_get(v_a_5975_, 1);
                    v_fst_5977_ = crate::leanh::lean_ctor_get(v_a_5975_, 0);
                    v_isSharedCheck_6078_ = (!crate::leanh::lean_is_exclusive(v_a_5975_)) as u8;
                    if v_isSharedCheck_6078_ == 0 {
                        v___x_5979_ = v_a_5975_;
                        v_isShared_5980_ = v_isSharedCheck_6078_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5976_);
                        crate::leanh::lean_inc(v_fst_5977_);
                        crate::leanh::lean_dec(v_a_5975_);
                        v___x_5979_ = crate::leanh::lean_box(0);
                        v_isShared_5980_ = v_isSharedCheck_6078_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_5953_);
                    crate::leanh::lean_dec_ref(v_proof_5952_);
                    v_a_6079_ = crate::leanh::lean_ctor_get(v___x_5974_, 0);
                    v_isSharedCheck_6086_ = (!crate::leanh::lean_is_exclusive(v___x_5974_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6081_ = v___x_5974_;
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6079_);
                        crate::leanh::lean_dec(v___x_5974_);
                        v___x_6081_ = crate::leanh::lean_box(0);
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_5981_ = crate::leanh::lean_ctor_get(v_snd_5976_, 1);
                v_isSharedCheck_6076_ = (!crate::leanh::lean_is_exclusive(v_snd_5976_)) as u8;
                if v_isSharedCheck_6076_ == 0 {
                    v_unused_6077_ = crate::leanh::lean_ctor_get(v_snd_5976_, 0);
                    crate::leanh::lean_dec(v_unused_6077_);
                    v___x_5983_ = v_snd_5976_;
                    v_isShared_5984_ = v_isSharedCheck_6076_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5981_);
                    crate::leanh::lean_dec(v_snd_5976_);
                    v___x_5983_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_5985_) == 0 {
                    v_a_5986_ = crate::leanh::lean_ctor_get(v___x_5985_, 0);
                    crate::leanh::lean_inc_n(v_a_5986_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5985_, 1);
                    v___x_5998_ = l_Lean_Expr_cleanupAnnotations(v_a_5986_);
                    v___x_5999_ = l_Lean_Expr_isApp(v___x_5998_);
                    if v___x_5999_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5998_);
                        crate::leanh::lean_del_object(v___x_5979_);
                        crate::leanh::lean_dec(v_fst_5977_);
                        crate::leanh::lean_dec(v_prio_5953_);
                        crate::leanh::lean_dec_ref(v_proof_5952_);
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
                            crate::leanh::lean_dec_ref(v___x_6000_);
                            crate::leanh::lean_del_object(v___x_5979_);
                            crate::leanh::lean_dec(v_fst_5977_);
                            crate::leanh::lean_dec(v_prio_5953_);
                            crate::leanh::lean_dec_ref(v_proof_5952_);
                            v___y_5988_ = v___y_5954_;
                            v___y_5989_ = v___y_5955_;
                            v___y_5990_ = v___y_5956_;
                            v___y_5991_ = v___y_5957_;
                            state = 3;
                            continue;
                        } else {
                            v_arg_6002_ = crate::leanh::lean_ctor_get(v___x_6000_, 1);
                            crate::leanh::lean_inc_ref(v_arg_6002_);
                            v___x_6003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6000_);
                            v___x_6004_ = l_Lean_Expr_isApp(v___x_6003_);
                            if v___x_6004_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_6003_);
                                crate::leanh::lean_dec_ref(v_arg_6002_);
                                crate::leanh::lean_del_object(v___x_5979_);
                                crate::leanh::lean_dec(v_fst_5977_);
                                crate::leanh::lean_dec(v_prio_5953_);
                                crate::leanh::lean_dec_ref(v_proof_5952_);
                                v___y_5988_ = v___y_5954_;
                                v___y_5989_ = v___y_5955_;
                                v___y_5990_ = v___y_5956_;
                                v___y_5991_ = v___y_5957_;
                                state = 3;
                                continue;
                            } else {
                                v_arg_6005_ = crate::leanh::lean_ctor_get(v___x_6003_, 1);
                                crate::leanh::lean_inc_ref(v_arg_6005_);
                                v___x_6006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6003_);
                                v___x_6007_ = l_Lean_Expr_isApp(v___x_6006_);
                                if v___x_6007_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_6006_);
                                    crate::leanh::lean_dec_ref(v_arg_6005_);
                                    crate::leanh::lean_dec_ref(v_arg_6002_);
                                    crate::leanh::lean_del_object(v___x_5979_);
                                    crate::leanh::lean_dec(v_fst_5977_);
                                    crate::leanh::lean_dec(v_prio_5953_);
                                    crate::leanh::lean_dec_ref(v_proof_5952_);
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
                                        crate::leanh::lean_dec_ref(v___x_6008_);
                                        crate::leanh::lean_dec_ref(v_arg_6005_);
                                        crate::leanh::lean_dec_ref(v_arg_6002_);
                                        crate::leanh::lean_del_object(v___x_5979_);
                                        crate::leanh::lean_dec(v_fst_5977_);
                                        crate::leanh::lean_dec(v_prio_5953_);
                                        crate::leanh::lean_dec_ref(v_proof_5952_);
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
                                            crate::leanh::lean_dec_ref(v___x_6010_);
                                            crate::leanh::lean_dec_ref(v_arg_6005_);
                                            crate::leanh::lean_dec_ref(v_arg_6002_);
                                            crate::leanh::lean_del_object(v___x_5979_);
                                            crate::leanh::lean_dec(v_fst_5977_);
                                            crate::leanh::lean_dec(v_prio_5953_);
                                            crate::leanh::lean_dec_ref(v_proof_5952_);
                                            v___y_5988_ = v___y_5954_;
                                            v___y_5989_ = v___y_5955_;
                                            v___y_5990_ = v___y_5956_;
                                            v___y_5991_ = v___y_5957_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_arg_6012_ =
                                                crate::leanh::lean_ctor_get(v___x_6010_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_6012_);
                                            v___x_6013_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_6010_);
                                            v___x_6014_ = l_Lean_Expr_isApp(v___x_6013_);
                                            if v___x_6014_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_6013_);
                                                crate::leanh::lean_dec_ref(v_arg_6012_);
                                                crate::leanh::lean_dec_ref(v_arg_6005_);
                                                crate::leanh::lean_dec_ref(v_arg_6002_);
                                                crate::leanh::lean_del_object(v___x_5979_);
                                                crate::leanh::lean_dec(v_fst_5977_);
                                                crate::leanh::lean_dec(v_prio_5953_);
                                                crate::leanh::lean_dec_ref(v_proof_5952_);
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
                                                    crate::leanh::lean_dec_ref(v___x_6015_);
                                                    crate::leanh::lean_dec_ref(v_arg_6012_);
                                                    crate::leanh::lean_dec_ref(v_arg_6005_);
                                                    crate::leanh::lean_dec_ref(v_arg_6002_);
                                                    crate::leanh::lean_del_object(v___x_5979_);
                                                    crate::leanh::lean_dec(v_fst_5977_);
                                                    crate::leanh::lean_dec(v_prio_5953_);
                                                    crate::leanh::lean_dec_ref(v_proof_5952_);
                                                    v___y_5988_ = v___y_5954_;
                                                    v___y_5989_ = v___y_5955_;
                                                    v___y_5990_ = v___y_5956_;
                                                    v___y_5991_ = v___y_5957_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_a_5986_);
                                                    crate::leanh::lean_del_object(v___x_5983_);
                                                    v___x_6018_ = 0;
                                                    crate::leanh::lean_inc_ref(v_arg_6005_);
                                                    v___x_6019_ = l_Lean_Meta_DiscrTree_mkPath(
                                                        v_arg_6005_,
                                                        v___x_6018_,
                                                        v___y_5954_,
                                                        v___y_5955_,
                                                        v___y_5956_,
                                                        v___y_5957_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_6019_) == 0
                                                    {
                                                        v_a_6020_ = crate::leanh::lean_ctor_get(
                                                            v___x_6019_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_6020_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_6019_,
                                                            1,
                                                        );
                                                        v___x_6021_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__7;
                                                        v___x_6022_ = l_Lean_Expr_constLevels_x21(
                                                            v___x_6015_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v___x_6015_);
                                                        v___x_6023_ =
                                                            crate::leanh::lean_unsigned_to_nat(0);
                                                        v___x_6024_ =
                                                            l_List_get_x21Internal___redArg(
                                                                v___x_5951_,
                                                                v___x_6022_,
                                                                v___x_6023_,
                                                            );
                                                        crate::leanh::lean_dec(v___x_6022_);
                                                        v___x_6025_ = crate::leanh::lean_box(0);
                                                        if v_isShared_5980_ == 0 {
                                                            crate::leanh::lean_ctor_set_tag(
                                                                v___x_5979_,
                                                                1,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_5979_,
                                                                1,
                                                                v___x_6025_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_5979_,
                                                                0,
                                                                v___x_6024_,
                                                            );
                                                            v___x_6027_ = v___x_5979_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_6059_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    1,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_6059_,
                                                                0,
                                                                v___x_6024_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_6059_,
                                                                1,
                                                                v___x_6025_,
                                                            );
                                                            v___x_6027_ = v_reuseFailAlloc_6059_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_6015_);
                                                        crate::leanh::lean_dec_ref(v_arg_6012_);
                                                        crate::leanh::lean_dec_ref(v_arg_6005_);
                                                        crate::leanh::lean_dec_ref(v_arg_6002_);
                                                        crate::leanh::lean_del_object(v___x_5979_);
                                                        crate::leanh::lean_dec(v_fst_5977_);
                                                        crate::leanh::lean_dec(v_prio_5953_);
                                                        crate::leanh::lean_dec_ref(v_proof_5952_);
                                                        v_a_6060_ = crate::leanh::lean_ctor_get(
                                                            v___x_6019_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_6067_ =
                                                            (!crate::leanh::lean_is_exclusive(
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
                                                            crate::leanh::lean_inc(v_a_6060_);
                                                            crate::leanh::lean_dec(v___x_6019_);
                                                            v___x_6062_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_del_object(v___x_5983_);
                    crate::leanh::lean_del_object(v___x_5979_);
                    crate::leanh::lean_dec(v_fst_5977_);
                    crate::leanh::lean_dec(v_prio_5953_);
                    crate::leanh::lean_dec_ref(v_proof_5952_);
                    v_a_6068_ = crate::leanh::lean_ctor_get(v___x_5985_, 0);
                    v_isSharedCheck_6075_ = (!crate::leanh::lean_is_exclusive(v___x_5985_)) as u8;
                    if v_isSharedCheck_6075_ == 0 {
                        v___x_6070_ = v___x_5985_;
                        v_isShared_6071_ = v_isSharedCheck_6075_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6068_);
                        crate::leanh::lean_dec(v___x_5985_);
                        v___x_6070_ = crate::leanh::lean_box(0);
                        v_isShared_6071_ = v_isSharedCheck_6075_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___closed__1);
                v___x_5993_ = l_Lean_indentExpr(v_a_5986_);
                if v_isShared_5984_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5983_, 7);
                    crate::leanh::lean_ctor_set(v___x_5983_, 1, v___x_5993_);
                    crate::leanh::lean_ctor_set(v___x_5983_, 0, v___x_5992_);
                    v___x_5995_ = v___x_5983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5997_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5997_, 0, v___x_5992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5997_, 1, v___x_5993_);
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
                crate::leanh::lean_inc(v_fst_5977_);
                v___x_6030_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
                    v_fst_5977_,
                    v___x_6029_,
                    v_arg_6002_,
                    v___y_5954_,
                    v___y_5955_,
                    v___y_5956_,
                    v___y_5957_,
                );
                if crate::leanh::lean_obj_tag(v___x_6030_) == 0 {
                    v_a_6031_ = crate::leanh::lean_ctor_get(v___x_6030_, 0);
                    crate::leanh::lean_inc(v_a_6031_);
                    crate::leanh::lean_dec_ref_known(v___x_6030_, 1);
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
                    crate::leanh::lean_dec(v_fst_5977_);
                    if crate::leanh::lean_obj_tag(v___x_6033_) == 0 {
                        v_a_6034_ = crate::leanh::lean_ctor_get(v___x_6033_, 0);
                        v_isSharedCheck_6042_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6033_)) as u8;
                        if v_isSharedCheck_6042_ == 0 {
                            v___x_6036_ = v___x_6033_;
                            v_isShared_6037_ = v_isSharedCheck_6042_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6034_);
                            crate::leanh::lean_dec(v___x_6033_);
                            v___x_6036_ = crate::leanh::lean_box(0);
                            v_isShared_6037_ = v_isSharedCheck_6042_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6031_);
                        crate::leanh::lean_dec(v_a_6020_);
                        crate::leanh::lean_dec(v_prio_5953_);
                        crate::leanh::lean_dec_ref(v_proof_5952_);
                        v_a_6043_ = crate::leanh::lean_ctor_get(v___x_6033_, 0);
                        v_isSharedCheck_6050_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6033_)) as u8;
                        if v_isSharedCheck_6050_ == 0 {
                            v___x_6045_ = v___x_6033_;
                            v_isShared_6046_ = v_isSharedCheck_6050_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6043_);
                            crate::leanh::lean_dec(v___x_6033_);
                            v___x_6045_ = crate::leanh::lean_box(0);
                            v_isShared_6046_ = v_isSharedCheck_6050_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6020_);
                    crate::leanh::lean_dec_ref(v_arg_6005_);
                    crate::leanh::lean_dec(v_fst_5977_);
                    crate::leanh::lean_dec(v_prio_5953_);
                    crate::leanh::lean_dec_ref(v_proof_5952_);
                    v_a_6051_ = crate::leanh::lean_ctor_get(v___x_6030_, 0);
                    v_isSharedCheck_6058_ = (!crate::leanh::lean_is_exclusive(v___x_6030_)) as u8;
                    if v_isSharedCheck_6058_ == 0 {
                        v___x_6053_ = v___x_6030_;
                        v_isShared_6054_ = v_isSharedCheck_6058_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6051_);
                        crate::leanh::lean_dec(v___x_6030_);
                        v___x_6053_ = crate::leanh::lean_box(0);
                        v_isShared_6054_ = v_isSharedCheck_6058_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6038_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6038_, 0, v_a_6020_);
                crate::leanh::lean_ctor_set(v___x_6038_, 1, v_a_6034_);
                crate::leanh::lean_ctor_set(v___x_6038_, 2, v_proof_5952_);
                crate::leanh::lean_ctor_set(v___x_6038_, 3, v_a_6031_);
                crate::leanh::lean_ctor_set(v___x_6038_, 4, v_prio_5953_);
                if v_isShared_6037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6036_, 0, v___x_6038_);
                    v___x_6040_ = v___x_6036_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6041_, 0, v___x_6038_);
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
                    v_reuseFailAlloc_6049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6049_, 0, v_a_6043_);
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
                    v_reuseFailAlloc_6057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
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
                    v_reuseFailAlloc_6066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
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
                    v_reuseFailAlloc_6074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6068_);
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
                    v_reuseFailAlloc_6085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
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
    mut v_a_6087_: *mut crate::leanh::LeanObject,
    mut v___x_6088_: *mut crate::leanh::LeanObject,
    mut v___x_6089_: *mut crate::leanh::LeanObject,
    mut v___x_6090_: *mut crate::leanh::LeanObject,
    mut v_proof_6091_: *mut crate::leanh::LeanObject,
    mut v_prio_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
    mut v___y_6094_: *mut crate::leanh::LeanObject,
    mut v___y_6095_: *mut crate::leanh::LeanObject,
    mut v___y_6096_: *mut crate::leanh::LeanObject,
    mut v___y_6097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3664__boxed_6098_: u8 = 0;
    let mut v_res_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3664__boxed_6098_ = (crate::leanh::lean_unbox(v___x_6089_) as u8);
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
    crate::leanh::lean_dec(v___y_6096_);
    crate::leanh::lean_dec_ref(v___y_6095_);
    crate::leanh::lean_dec(v___y_6094_);
    crate::leanh::lean_dec_ref(v___y_6093_);
    crate::leanh::lean_dec(v___x_6090_);
    return v_res_6099_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6101_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__0;
    v___x_6102_ = l_Lean_stringToMessageData(v___x_6101_);
    return v___x_6102_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(
    mut v_type_6103_: *mut crate::leanh::LeanObject,
    mut v_proof_6104_: *mut crate::leanh::LeanObject,
    mut v_prio_6105_: *mut crate::leanh::LeanObject,
    mut v_a_6106_: *mut crate::leanh::LeanObject,
    mut v_a_6107_: *mut crate::leanh::LeanObject,
    mut v_a_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: u8 = 0;
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: u8 = 0;
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: u8 = 0;
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6135_: u8 = 0;
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6139_: u8 = 0;
    let mut v_a_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6111_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate_spec__0___redArg(v_type_6103_, v_a_6107_);
                v_a_6112_ = crate::leanh::lean_ctor_get(v___x_6111_, 0);
                crate::leanh::lean_inc_n(v_a_6112_, 2);
                crate::leanh::lean_dec_ref(v___x_6111_);
                v___x_6113_ =
                    l_Lean_Meta_isProp(v_a_6112_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_);
                if crate::leanh::lean_obj_tag(v___x_6113_) == 0 {
                    v_a_6114_ = crate::leanh::lean_ctor_get(v___x_6113_, 0);
                    crate::leanh::lean_inc(v_a_6114_);
                    crate::leanh::lean_dec_ref_known(v___x_6113_, 1);
                    v___x_6115_ = crate::leanh::lean_box(0);
                    v___x_6127_ = (crate::leanh::lean_unbox(v_a_6114_) as u8);
                    crate::leanh::lean_dec(v_a_6114_);
                    if v___x_6127_ == 0 {
                        crate::leanh::lean_dec(v_prio_6105_);
                        crate::leanh::lean_dec_ref(v_proof_6104_);
                        v___x_6128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1_once), _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___closed__1);
                        v___x_6129_ = l_Lean_indentExpr(v_a_6112_);
                        v___x_6130_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6130_, 0, v___x_6128_);
                        crate::leanh::lean_ctor_set(v___x_6130_, 1, v___x_6129_);
                        v___x_6131_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_6130_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_);
                        v_a_6132_ = crate::leanh::lean_ctor_get(v___x_6131_, 0);
                        v_isSharedCheck_6139_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6131_)) as u8;
                        if v_isSharedCheck_6139_ == 0 {
                            v___x_6134_ = v___x_6131_;
                            v_isShared_6135_ = v_isSharedCheck_6139_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6132_);
                            crate::leanh::lean_dec(v___x_6131_);
                            v___x_6134_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v_a_6112_);
                    crate::leanh::lean_dec(v_prio_6105_);
                    crate::leanh::lean_dec_ref(v_proof_6104_);
                    v_a_6140_ = crate::leanh::lean_ctor_get(v___x_6113_, 0);
                    v_isSharedCheck_6147_ = (!crate::leanh::lean_is_exclusive(v___x_6113_)) as u8;
                    if v_isSharedCheck_6147_ == 0 {
                        v___x_6142_ = v___x_6113_;
                        v_isShared_6143_ = v_isSharedCheck_6147_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6140_);
                        crate::leanh::lean_dec(v___x_6113_);
                        v___x_6142_ = crate::leanh::lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6147_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6121_ = crate::leanh::lean_box(0);
                v___x_6122_ = 0;
                v___x_6123_ = crate::leanh::lean_box((v___x_6122_) as usize);
                v___f_6124_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_6124_, 0, v_a_6112_);
                crate::leanh::lean_closure_set(v___f_6124_, 1, v___x_6121_);
                crate::leanh::lean_closure_set(v___f_6124_, 2, v___x_6123_);
                crate::leanh::lean_closure_set(v___f_6124_, 3, v___x_6115_);
                crate::leanh::lean_closure_set(v___f_6124_, 4, v_proof_6104_);
                crate::leanh::lean_closure_set(v___f_6124_, 5, v_prio_6105_);
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
                    v_reuseFailAlloc_6138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6138_, 0, v_a_6132_);
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
                    v_reuseFailAlloc_6146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_a_6140_);
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
    mut v_type_6148_: *mut crate::leanh::LeanObject,
    mut v_proof_6149_: *mut crate::leanh::LeanObject,
    mut v_prio_6150_: *mut crate::leanh::LeanObject,
    mut v_a_6151_: *mut crate::leanh::LeanObject,
    mut v_a_6152_: *mut crate::leanh::LeanObject,
    mut v_a_6153_: *mut crate::leanh::LeanObject,
    mut v_a_6154_: *mut crate::leanh::LeanObject,
    mut v_a_6155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_6154_);
    crate::leanh::lean_dec_ref(v_a_6153_);
    crate::leanh::lean_dec(v_a_6152_);
    crate::leanh::lean_dec_ref(v_a_6151_);
    return v_res_6156_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(
    mut v_declName_6157_: *mut crate::leanh::LeanObject,
    mut v_prio_6158_: *mut crate::leanh::LeanObject,
    mut v_a_6159_: *mut crate::leanh::LeanObject,
    mut v_a_6160_: *mut crate::leanh::LeanObject,
    mut v_a_6161_: *mut crate::leanh::LeanObject,
    mut v_a_6162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut v_a_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_6157_);
                v___x_6164_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0(v_declName_6157_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
                if crate::leanh::lean_obj_tag(v___x_6164_) == 0 {
                    v_a_6165_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                    crate::leanh::lean_inc(v_a_6165_);
                    crate::leanh::lean_dec_ref_known(v___x_6164_, 1);
                    v___x_6166_ = l_Lean_ConstantInfo_levelParams(v_a_6165_);
                    crate::leanh::lean_dec(v_a_6165_);
                    v___x_6167_ = crate::leanh::lean_box(0);
                    v___x_6168_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__1(v___x_6166_, v___x_6167_);
                    crate::leanh::lean_inc(v_declName_6157_);
                    v___x_6169_ = l_Lean_mkConst(v_declName_6157_, v___x_6168_);
                    crate::leanh::lean_inc(v_a_6162_);
                    crate::leanh::lean_inc_ref(v_a_6161_);
                    crate::leanh::lean_inc(v_a_6160_);
                    crate::leanh::lean_inc_ref(v_a_6159_);
                    v___x_6170_ =
                        lean_infer_type(v___x_6169_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
                    if crate::leanh::lean_obj_tag(v___x_6170_) == 0 {
                        v_a_6171_ = crate::leanh::lean_ctor_get(v___x_6170_, 0);
                        crate::leanh::lean_inc(v_a_6171_);
                        crate::leanh::lean_dec_ref_known(v___x_6170_, 1);
                        v___x_6172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6172_, 0, v_declName_6157_);
                        v___x_6173_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_6171_, v___x_6172_, v_prio_6158_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
                        return v___x_6173_;
                    } else {
                        crate::leanh::lean_dec(v_prio_6158_);
                        crate::leanh::lean_dec(v_declName_6157_);
                        v_a_6174_ = crate::leanh::lean_ctor_get(v___x_6170_, 0);
                        v_isSharedCheck_6181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6170_)) as u8;
                        if v_isSharedCheck_6181_ == 0 {
                            v___x_6176_ = v___x_6170_;
                            v_isShared_6177_ = v_isSharedCheck_6181_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6174_);
                            crate::leanh::lean_dec(v___x_6170_);
                            v___x_6176_ = crate::leanh::lean_box(0);
                            v_isShared_6177_ = v_isSharedCheck_6181_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_6158_);
                    crate::leanh::lean_dec(v_declName_6157_);
                    v_a_6182_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                    v_isSharedCheck_6189_ = (!crate::leanh::lean_is_exclusive(v___x_6164_)) as u8;
                    if v_isSharedCheck_6189_ == 0 {
                        v___x_6184_ = v___x_6164_;
                        v_isShared_6185_ = v_isSharedCheck_6189_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6182_);
                        crate::leanh::lean_dec(v___x_6164_);
                        v___x_6184_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_a_6174_);
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
                    v_reuseFailAlloc_6188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
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
    mut v_declName_6190_: *mut crate::leanh::LeanObject,
    mut v_prio_6191_: *mut crate::leanh::LeanObject,
    mut v_a_6192_: *mut crate::leanh::LeanObject,
    mut v_a_6193_: *mut crate::leanh::LeanObject,
    mut v_a_6194_: *mut crate::leanh::LeanObject,
    mut v_a_6195_: *mut crate::leanh::LeanObject,
    mut v_a_6196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6197_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(
        v_declName_6190_,
        v_prio_6191_,
        v_a_6192_,
        v_a_6193_,
        v_a_6194_,
        v_a_6195_,
    );
    crate::leanh::lean_dec(v_a_6195_);
    crate::leanh::lean_dec_ref(v_a_6194_);
    crate::leanh::lean_dec(v_a_6193_);
    crate::leanh::lean_dec_ref(v_a_6192_);
    return v_res_6197_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6199_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__0;
    v___x_6200_ = l_Lean_stringToMessageData(v___x_6199_);
    return v___x_6200_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6202_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__2;
    v___x_6203_ = l_Lean_stringToMessageData(v___x_6202_);
    return v___x_6203_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(
    mut v_fvar_6204_: *mut crate::leanh::LeanObject,
    mut v_prio_6205_: *mut crate::leanh::LeanObject,
    mut v_a_6206_: *mut crate::leanh::LeanObject,
    mut v_a_6207_: *mut crate::leanh::LeanObject,
    mut v_a_6208_: *mut crate::leanh::LeanObject,
    mut v_a_6209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6216_: u8 = 0;
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6222_: u8 = 0;
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6232_: u8 = 0;
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvar_6204_);
                v___x_6211_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvar_6204_, v_a_6206_);
                if crate::leanh::lean_obj_tag(v___x_6211_) == 0 {
                    v_a_6212_ = crate::leanh::lean_ctor_get(v___x_6211_, 0);
                    crate::leanh::lean_inc(v_a_6212_);
                    crate::leanh::lean_dec_ref_known(v___x_6211_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6212_) == 1 {
                        v_val_6213_ = crate::leanh::lean_ctor_get(v_a_6212_, 0);
                        v_isSharedCheck_6222_ = (!crate::leanh::lean_is_exclusive(v_a_6212_)) as u8;
                        if v_isSharedCheck_6222_ == 0 {
                            v___x_6215_ = v_a_6212_;
                            v_isShared_6216_ = v_isSharedCheck_6222_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6213_);
                            crate::leanh::lean_dec(v_a_6212_);
                            v___x_6215_ = crate::leanh::lean_box(0);
                            v_isShared_6216_ = v_isSharedCheck_6222_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6212_);
                        crate::leanh::lean_dec(v_prio_6205_);
                        v___x_6223_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__1);
                        v___x_6224_ = l_Lean_MessageData_ofName(v_fvar_6204_);
                        v___x_6225_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6225_, 0, v___x_6223_);
                        crate::leanh::lean_ctor_set(v___x_6225_, 1, v___x_6224_);
                        v___x_6226_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal___closed__3);
                        v___x_6227_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6227_, 0, v___x_6225_);
                        crate::leanh::lean_ctor_set(v___x_6227_, 1, v___x_6226_);
                        v___x_6228_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v___x_6227_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_);
                        return v___x_6228_;
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_6205_);
                    crate::leanh::lean_dec(v_fvar_6204_);
                    v_a_6229_ = crate::leanh::lean_ctor_get(v___x_6211_, 0);
                    v_isSharedCheck_6236_ = (!crate::leanh::lean_is_exclusive(v___x_6211_)) as u8;
                    if v_isSharedCheck_6236_ == 0 {
                        v___x_6231_ = v___x_6211_;
                        v_isShared_6232_ = v_isSharedCheck_6236_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6229_);
                        crate::leanh::lean_dec(v___x_6211_);
                        v___x_6231_ = crate::leanh::lean_box(0);
                        v_isShared_6232_ = v_isSharedCheck_6236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6217_ = l_Lean_LocalDecl_type(v_val_6213_);
                crate::leanh::lean_dec(v_val_6213_);
                if v_isShared_6216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6215_, 0, v_fvar_6204_);
                    v___x_6219_ = v___x_6215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6221_, 0, v_fvar_6204_);
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
                    v_reuseFailAlloc_6235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6235_, 0, v_a_6229_);
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
    mut v_fvar_6237_: *mut crate::leanh::LeanObject,
    mut v_prio_6238_: *mut crate::leanh::LeanObject,
    mut v_a_6239_: *mut crate::leanh::LeanObject,
    mut v_a_6240_: *mut crate::leanh::LeanObject,
    mut v_a_6241_: *mut crate::leanh::LeanObject,
    mut v_a_6242_: *mut crate::leanh::LeanObject,
    mut v_a_6243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6244_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(
        v_fvar_6237_,
        v_prio_6238_,
        v_a_6239_,
        v_a_6240_,
        v_a_6241_,
        v_a_6242_,
    );
    crate::leanh::lean_dec(v_a_6242_);
    crate::leanh::lean_dec_ref(v_a_6241_);
    crate::leanh::lean_dec(v_a_6240_);
    crate::leanh::lean_dec_ref(v_a_6239_);
    return v_res_6244_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(
    mut v___y_6245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6253_: u8 = 0;
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v_r_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut v_unused_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6247_ = lean_st_ref_get(v___y_6245_);
                v_ngen_6248_ = crate::leanh::lean_ctor_get(v___x_6247_, 2);
                crate::leanh::lean_inc_ref(v_ngen_6248_);
                crate::leanh::lean_dec(v___x_6247_);
                v_namePrefix_6249_ = crate::leanh::lean_ctor_get(v_ngen_6248_, 0);
                v_idx_6250_ = crate::leanh::lean_ctor_get(v_ngen_6248_, 1);
                v_isSharedCheck_6279_ = (!crate::leanh::lean_is_exclusive(v_ngen_6248_)) as u8;
                if v_isSharedCheck_6279_ == 0 {
                    v___x_6252_ = v_ngen_6248_;
                    v_isShared_6253_ = v_isSharedCheck_6279_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_6250_);
                    crate::leanh::lean_inc(v_namePrefix_6249_);
                    crate::leanh::lean_dec(v_ngen_6248_);
                    v___x_6252_ = crate::leanh::lean_box(0);
                    v_isShared_6253_ = v_isSharedCheck_6279_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6254_ = lean_st_ref_take(v___y_6245_);
                v_env_6255_ = crate::leanh::lean_ctor_get(v___x_6254_, 0);
                v_nextMacroScope_6256_ = crate::leanh::lean_ctor_get(v___x_6254_, 1);
                v_auxDeclNGen_6257_ = crate::leanh::lean_ctor_get(v___x_6254_, 3);
                v_traceState_6258_ = crate::leanh::lean_ctor_get(v___x_6254_, 4);
                v_cache_6259_ = crate::leanh::lean_ctor_get(v___x_6254_, 5);
                v_messages_6260_ = crate::leanh::lean_ctor_get(v___x_6254_, 6);
                v_infoState_6261_ = crate::leanh::lean_ctor_get(v___x_6254_, 7);
                v_snapshotTasks_6262_ = crate::leanh::lean_ctor_get(v___x_6254_, 8);
                v_isSharedCheck_6277_ = (!crate::leanh::lean_is_exclusive(v___x_6254_)) as u8;
                if v_isSharedCheck_6277_ == 0 {
                    v_unused_6278_ = crate::leanh::lean_ctor_get(v___x_6254_, 2);
                    crate::leanh::lean_dec(v_unused_6278_);
                    v___x_6264_ = v___x_6254_;
                    v_isShared_6265_ = v_isSharedCheck_6277_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6262_);
                    crate::leanh::lean_inc(v_infoState_6261_);
                    crate::leanh::lean_inc(v_messages_6260_);
                    crate::leanh::lean_inc(v_cache_6259_);
                    crate::leanh::lean_inc(v_traceState_6258_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6257_);
                    crate::leanh::lean_inc(v_nextMacroScope_6256_);
                    crate::leanh::lean_inc(v_env_6255_);
                    crate::leanh::lean_dec(v___x_6254_);
                    v___x_6264_ = crate::leanh::lean_box(0);
                    v_isShared_6265_ = v_isSharedCheck_6277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_6250_);
                crate::leanh::lean_inc(v_namePrefix_6249_);
                v_r_6266_ = l_Lean_Name_num___override(v_namePrefix_6249_, v_idx_6250_);
                v___x_6267_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6268_ = lean_nat_add(v_idx_6250_, v___x_6267_);
                crate::leanh::lean_dec(v_idx_6250_);
                if v_isShared_6253_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6252_, 1, v___x_6268_);
                    v___x_6270_ = v___x_6252_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_namePrefix_6249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 1, v___x_6268_);
                    v___x_6270_ = v_reuseFailAlloc_6276_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6264_, 2, v___x_6270_);
                    v___x_6272_ = v___x_6264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6275_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_env_6255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 1, v_nextMacroScope_6256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 2, v___x_6270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 3, v_auxDeclNGen_6257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 4, v_traceState_6258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 5, v_cache_6259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 6, v_messages_6260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 7, v_infoState_6261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 8, v_snapshotTasks_6262_);
                    v___x_6272_ = v_reuseFailAlloc_6275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6273_ = lean_st_ref_set(v___y_6245_, v___x_6272_);
                v___x_6274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6274_, 0, v_r_6266_);
                return v___x_6274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg___boxed(
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6282_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_6280_);
    crate::leanh::lean_dec(v___y_6280_);
    return v_res_6282_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(
    mut v___y_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v___y_6286_);
    return v___x_6288_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___boxed(
    mut v___y_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6294_ =
        l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0(
            v___y_6289_,
            v___y_6290_,
            v___y_6291_,
            v___y_6292_,
        );
    crate::leanh::lean_dec(v___y_6292_);
    crate::leanh::lean_dec_ref(v___y_6291_);
    crate::leanh::lean_dec(v___y_6290_);
    crate::leanh::lean_dec_ref(v___y_6289_);
    return v_res_6294_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(
    mut v_ref_6295_: *mut crate::leanh::LeanObject,
    mut v_proof_6296_: *mut crate::leanh::LeanObject,
    mut v_prio_6297_: *mut crate::leanh::LeanObject,
    mut v_a_6298_: *mut crate::leanh::LeanObject,
    mut v_a_6299_: *mut crate::leanh::LeanObject,
    mut v_a_6300_: *mut crate::leanh::LeanObject,
    mut v_a_6301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6312_: u8 = 0;
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6301_);
                crate::leanh::lean_inc_ref(v_a_6300_);
                crate::leanh::lean_inc(v_a_6299_);
                crate::leanh::lean_inc_ref(v_a_6298_);
                crate::leanh::lean_inc_ref(v_proof_6296_);
                v___x_6303_ =
                    lean_infer_type(v_proof_6296_, v_a_6298_, v_a_6299_, v_a_6300_, v_a_6301_);
                if crate::leanh::lean_obj_tag(v___x_6303_) == 0 {
                    v_a_6304_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                    crate::leanh::lean_inc(v_a_6304_);
                    crate::leanh::lean_dec_ref_known(v___x_6303_, 1);
                    v___x_6305_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx_spec__0___redArg(v_a_6301_);
                    v_a_6306_ = crate::leanh::lean_ctor_get(v___x_6305_, 0);
                    crate::leanh::lean_inc(v_a_6306_);
                    crate::leanh::lean_dec_ref(v___x_6305_);
                    v___x_6307_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6307_, 0, v_a_6306_);
                    crate::leanh::lean_ctor_set(v___x_6307_, 1, v_ref_6295_);
                    crate::leanh::lean_ctor_set(v___x_6307_, 2, v_proof_6296_);
                    v___x_6308_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheorem(v_a_6304_, v___x_6307_, v_prio_6297_, v_a_6298_, v_a_6299_, v_a_6300_, v_a_6301_);
                    return v___x_6308_;
                } else {
                    crate::leanh::lean_dec(v_prio_6297_);
                    crate::leanh::lean_dec_ref(v_proof_6296_);
                    crate::leanh::lean_dec(v_ref_6295_);
                    v_a_6309_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                    v_isSharedCheck_6316_ = (!crate::leanh::lean_is_exclusive(v___x_6303_)) as u8;
                    if v_isSharedCheck_6316_ == 0 {
                        v___x_6311_ = v___x_6303_;
                        v_isShared_6312_ = v_isSharedCheck_6316_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6309_);
                        crate::leanh::lean_dec(v___x_6303_);
                        v___x_6311_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6315_, 0, v_a_6309_);
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
    mut v_ref_6317_: *mut crate::leanh::LeanObject,
    mut v_proof_6318_: *mut crate::leanh::LeanObject,
    mut v_prio_6319_: *mut crate::leanh::LeanObject,
    mut v_a_6320_: *mut crate::leanh::LeanObject,
    mut v_a_6321_: *mut crate::leanh::LeanObject,
    mut v_a_6322_: *mut crate::leanh::LeanObject,
    mut v_a_6323_: *mut crate::leanh::LeanObject,
    mut v_a_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromStx(
        v_ref_6317_,
        v_proof_6318_,
        v_prio_6319_,
        v_a_6320_,
        v_a_6321_,
        v_a_6322_,
        v_a_6323_,
    );
    crate::leanh::lean_dec(v_a_6323_);
    crate::leanh::lean_dec_ref(v_a_6322_);
    crate::leanh::lean_dec(v_a_6321_);
    crate::leanh::lean_dec_ref(v_a_6320_);
    return v_res_6325_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6326_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6326_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6327_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__0);
    v___x_6328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6328_, 0, v___x_6327_);
    return v___x_6328_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6329_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
    v___x_6330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6330_, 0, v___x_6329_);
    crate::leanh::lean_ctor_set(v___x_6330_, 1, v___x_6329_);
    return v___x_6330_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__1);
    v___x_6332_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6332_, 0, v___x_6331_);
    crate::leanh::lean_ctor_set(v___x_6332_, 1, v___x_6331_);
    crate::leanh::lean_ctor_set(v___x_6332_, 2, v___x_6331_);
    crate::leanh::lean_ctor_set(v___x_6332_, 3, v___x_6331_);
    crate::leanh::lean_ctor_set(v___x_6332_, 4, v___x_6331_);
    crate::leanh::lean_ctor_set(v___x_6332_, 5, v___x_6331_);
    return v___x_6332_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(
    mut v_ext_6333_: *mut crate::leanh::LeanObject,
    mut v_b_6334_: *mut crate::leanh::LeanObject,
    mut v_kind_6335_: u8,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currNamespace_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6352_: u8 = 0;
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_unused_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6376_: u8 = 0;
    let mut v_unused_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_6340_ = crate::leanh::lean_ctor_get(v___y_6337_, 6);
                v___x_6341_ = lean_st_ref_take(v___y_6338_);
                v_env_6342_ = crate::leanh::lean_ctor_get(v___x_6341_, 0);
                v_nextMacroScope_6343_ = crate::leanh::lean_ctor_get(v___x_6341_, 1);
                v_ngen_6344_ = crate::leanh::lean_ctor_get(v___x_6341_, 2);
                v_auxDeclNGen_6345_ = crate::leanh::lean_ctor_get(v___x_6341_, 3);
                v_traceState_6346_ = crate::leanh::lean_ctor_get(v___x_6341_, 4);
                v_messages_6347_ = crate::leanh::lean_ctor_get(v___x_6341_, 6);
                v_infoState_6348_ = crate::leanh::lean_ctor_get(v___x_6341_, 7);
                v_snapshotTasks_6349_ = crate::leanh::lean_ctor_get(v___x_6341_, 8);
                v_isSharedCheck_6376_ = (!crate::leanh::lean_is_exclusive(v___x_6341_)) as u8;
                if v_isSharedCheck_6376_ == 0 {
                    v_unused_6377_ = crate::leanh::lean_ctor_get(v___x_6341_, 5);
                    crate::leanh::lean_dec(v_unused_6377_);
                    v___x_6351_ = v___x_6341_;
                    v_isShared_6352_ = v_isSharedCheck_6376_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6349_);
                    crate::leanh::lean_inc(v_infoState_6348_);
                    crate::leanh::lean_inc(v_messages_6347_);
                    crate::leanh::lean_inc(v_traceState_6346_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6345_);
                    crate::leanh::lean_inc(v_ngen_6344_);
                    crate::leanh::lean_inc(v_nextMacroScope_6343_);
                    crate::leanh::lean_inc(v_env_6342_);
                    crate::leanh::lean_dec(v___x_6341_);
                    v___x_6351_ = crate::leanh::lean_box(0);
                    v_isShared_6352_ = v_isSharedCheck_6376_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_currNamespace_6340_);
                v___x_6353_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_6342_,
                    v_ext_6333_,
                    v_b_6334_,
                    v_kind_6335_,
                    v_currNamespace_6340_,
                );
                v___x_6354_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__2);
                if v_isShared_6352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6351_, 5, v___x_6354_);
                    crate::leanh::lean_ctor_set(v___x_6351_, 0, v___x_6353_);
                    v___x_6356_ = v___x_6351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6375_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 0, v___x_6353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 1, v_nextMacroScope_6343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 2, v_ngen_6344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 3, v_auxDeclNGen_6345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 4, v_traceState_6346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 5, v___x_6354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 6, v_messages_6347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 7, v_infoState_6348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 8, v_snapshotTasks_6349_);
                    v___x_6356_ = v_reuseFailAlloc_6375_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6357_ = lean_st_ref_set(v___y_6338_, v___x_6356_);
                v___x_6358_ = lean_st_ref_take(v___y_6336_);
                v_mctx_6359_ = crate::leanh::lean_ctor_get(v___x_6358_, 0);
                v_zetaDeltaFVarIds_6360_ = crate::leanh::lean_ctor_get(v___x_6358_, 2);
                v_postponed_6361_ = crate::leanh::lean_ctor_get(v___x_6358_, 3);
                v_diag_6362_ = crate::leanh::lean_ctor_get(v___x_6358_, 4);
                v_isSharedCheck_6373_ = (!crate::leanh::lean_is_exclusive(v___x_6358_)) as u8;
                if v_isSharedCheck_6373_ == 0 {
                    v_unused_6374_ = crate::leanh::lean_ctor_get(v___x_6358_, 1);
                    crate::leanh::lean_dec(v_unused_6374_);
                    v___x_6364_ = v___x_6358_;
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6362_);
                    crate::leanh::lean_inc(v_postponed_6361_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6360_);
                    crate::leanh::lean_inc(v_mctx_6359_);
                    crate::leanh::lean_dec(v___x_6358_);
                    v___x_6364_ = crate::leanh::lean_box(0);
                    v_isShared_6365_ = v_isSharedCheck_6373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6366_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___closed__3);
                if v_isShared_6365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6364_, 1, v___x_6366_);
                    v___x_6368_ = v___x_6364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6372_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_mctx_6359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 1, v___x_6366_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6372_,
                        2,
                        v_zetaDeltaFVarIds_6360_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 3, v_postponed_6361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 4, v_diag_6362_);
                    v___x_6368_ = v_reuseFailAlloc_6372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6369_ = lean_st_ref_set(v___y_6336_, v___x_6368_);
                v___x_6370_ = crate::leanh::lean_box(0);
                v___x_6371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6371_, 0, v___x_6370_);
                return v___x_6371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg___boxed(
    mut v_ext_6378_: *mut crate::leanh::LeanObject,
    mut v_b_6379_: *mut crate::leanh::LeanObject,
    mut v_kind_6380_: *mut crate::leanh::LeanObject,
    mut v___y_6381_: *mut crate::leanh::LeanObject,
    mut v___y_6382_: *mut crate::leanh::LeanObject,
    mut v___y_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6385_: u8 = 0;
    let mut v_res_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6385_ = (crate::leanh::lean_unbox(v_kind_6380_) as u8);
    v_res_6386_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6378_, v_b_6379_, v_kind_boxed_6385_, v___y_6381_, v___y_6382_, v___y_6383_);
    crate::leanh::lean_dec(v___y_6383_);
    crate::leanh::lean_dec_ref(v___y_6382_);
    crate::leanh::lean_dec(v___y_6381_);
    return v_res_6386_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(
    mut v_00_u03b1_6387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6388_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6389_: *mut crate::leanh::LeanObject,
    mut v_ext_6390_: *mut crate::leanh::LeanObject,
    mut v_b_6391_: *mut crate::leanh::LeanObject,
    mut v_kind_6392_: u8,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
    mut v___y_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6398_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6390_, v_b_6391_, v_kind_6392_, v___y_6394_, v___y_6395_, v___y_6396_);
    return v___x_6398_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___boxed(
    mut v_00_u03b1_6399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6400_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6401_: *mut crate::leanh::LeanObject,
    mut v_ext_6402_: *mut crate::leanh::LeanObject,
    mut v_b_6403_: *mut crate::leanh::LeanObject,
    mut v_kind_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
    mut v___y_6406_: *mut crate::leanh::LeanObject,
    mut v___y_6407_: *mut crate::leanh::LeanObject,
    mut v___y_6408_: *mut crate::leanh::LeanObject,
    mut v___y_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_6410_: u8 = 0;
    let mut v_res_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6410_ = (crate::leanh::lean_unbox(v_kind_6404_) as u8);
    v_res_6411_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0(v_00_u03b1_6399_, v_00_u03b2_6400_, v_00_u03c3_6401_, v_ext_6402_, v_b_6403_, v_kind_boxed_6410_, v___y_6405_, v___y_6406_, v___y_6407_, v___y_6408_);
    crate::leanh::lean_dec(v___y_6408_);
    crate::leanh::lean_dec_ref(v___y_6407_);
    crate::leanh::lean_dec(v___y_6406_);
    crate::leanh::lean_dec_ref(v___y_6405_);
    return v_res_6411_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst(
    mut v_ext_6412_: *mut crate::leanh::LeanObject,
    mut v_declName_6413_: *mut crate::leanh::LeanObject,
    mut v_prio_6414_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6415_: u8,
    mut v_a_6416_: *mut crate::leanh::LeanObject,
    mut v_a_6417_: *mut crate::leanh::LeanObject,
    mut v_a_6418_: *mut crate::leanh::LeanObject,
    mut v_a_6419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6427_: u8 = 0;
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_6421_) == 0 {
                    v_a_6422_ = crate::leanh::lean_ctor_get(v___x_6421_, 0);
                    crate::leanh::lean_inc(v_a_6422_);
                    crate::leanh::lean_dec_ref_known(v___x_6421_, 1);
                    v___x_6423_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6412_, v_a_6422_, v_attrKind_6415_, v_a_6417_, v_a_6418_, v_a_6419_);
                    return v___x_6423_;
                } else {
                    crate::leanh::lean_dec_ref(v_ext_6412_);
                    v_a_6424_ = crate::leanh::lean_ctor_get(v___x_6421_, 0);
                    v_isSharedCheck_6431_ = (!crate::leanh::lean_is_exclusive(v___x_6421_)) as u8;
                    if v_isSharedCheck_6431_ == 0 {
                        v___x_6426_ = v___x_6421_;
                        v_isShared_6427_ = v_isSharedCheck_6431_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6424_);
                        crate::leanh::lean_dec(v___x_6421_);
                        v___x_6426_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6424_);
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
    mut v_ext_6432_: *mut crate::leanh::LeanObject,
    mut v_declName_6433_: *mut crate::leanh::LeanObject,
    mut v_prio_6434_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6435_: *mut crate::leanh::LeanObject,
    mut v_a_6436_: *mut crate::leanh::LeanObject,
    mut v_a_6437_: *mut crate::leanh::LeanObject,
    mut v_a_6438_: *mut crate::leanh::LeanObject,
    mut v_a_6439_: *mut crate::leanh::LeanObject,
    mut v_a_6440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_6441_: u8 = 0;
    let mut v_res_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6441_ = (crate::leanh::lean_unbox(v_attrKind_6435_) as u8);
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
    crate::leanh::lean_dec(v_a_6439_);
    crate::leanh::lean_dec_ref(v_a_6438_);
    crate::leanh::lean_dec(v_a_6437_);
    crate::leanh::lean_dec_ref(v_a_6436_);
    return v_res_6442_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(
    mut v_ext_6443_: *mut crate::leanh::LeanObject,
    mut v_fvar_6444_: *mut crate::leanh::LeanObject,
    mut v_prio_6445_: *mut crate::leanh::LeanObject,
    mut v_a_6446_: *mut crate::leanh::LeanObject,
    mut v_a_6447_: *mut crate::leanh::LeanObject,
    mut v_a_6448_: *mut crate::leanh::LeanObject,
    mut v_a_6449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: u8 = 0;
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6458_: u8 = 0;
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_6451_) == 0 {
                    v_a_6452_ = crate::leanh::lean_ctor_get(v___x_6451_, 0);
                    crate::leanh::lean_inc(v_a_6452_);
                    crate::leanh::lean_dec_ref_known(v___x_6451_, 1);
                    v___x_6453_ = 1;
                    v___x_6454_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromConst_spec__0___redArg(v_ext_6443_, v_a_6452_, v___x_6453_, v_a_6447_, v_a_6448_, v_a_6449_);
                    return v___x_6454_;
                } else {
                    crate::leanh::lean_dec_ref(v_ext_6443_);
                    v_a_6455_ = crate::leanh::lean_ctor_get(v___x_6451_, 0);
                    v_isSharedCheck_6462_ = (!crate::leanh::lean_is_exclusive(v___x_6451_)) as u8;
                    if v_isSharedCheck_6462_ == 0 {
                        v___x_6457_ = v___x_6451_;
                        v_isShared_6458_ = v_isSharedCheck_6462_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6455_);
                        crate::leanh::lean_dec(v___x_6451_);
                        v___x_6457_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
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
    mut v_ext_6463_: *mut crate::leanh::LeanObject,
    mut v_fvar_6464_: *mut crate::leanh::LeanObject,
    mut v_prio_6465_: *mut crate::leanh::LeanObject,
    mut v_a_6466_: *mut crate::leanh::LeanObject,
    mut v_a_6467_: *mut crate::leanh::LeanObject,
    mut v_a_6468_: *mut crate::leanh::LeanObject,
    mut v_a_6469_: *mut crate::leanh::LeanObject,
    mut v_a_6470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6471_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_addSpecTheoremFromLocal(
        v_ext_6463_,
        v_fvar_6464_,
        v_prio_6465_,
        v_a_6466_,
        v_a_6467_,
        v_a_6468_,
        v_a_6469_,
    );
    crate::leanh::lean_dec(v_a_6469_);
    crate::leanh::lean_dec_ref(v_a_6468_);
    crate::leanh::lean_dec(v_a_6467_);
    crate::leanh::lean_dec_ref(v_a_6466_);
    return v_res_6471_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(
    mut v_x_6472_: *mut crate::leanh::LeanObject,
    mut v_a_6473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6474_, 0, v_a_6473_);
    crate::leanh::lean_inc_ref_n(v___x_6474_, 2);
    v___x_6475_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6475_, 0, v___x_6474_);
    crate::leanh::lean_ctor_set(v___x_6475_, 1, v___x_6474_);
    crate::leanh::lean_ctor_set(v___x_6475_, 2, v___x_6474_);
    return v___x_6475_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0___boxed(
    mut v_x_6476_: *mut crate::leanh::LeanObject,
    mut v_a_6477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6478_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__0(v_x_6476_, v_a_6477_);
    crate::leanh::lean_dec_ref(v_x_6476_);
    return v_res_6478_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(
    mut v___y_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___y_6479_);
    return v___y_6479_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1___boxed(
    mut v___y_6480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6481_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___lam__1(v___y_6480_);
    crate::leanh::lean_dec_ref(v___y_6480_);
    return v_res_6481_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6488_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__1;
    v___f_6489_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__2;
    v___x_6490_ = crate::leanh::lean_obj_once(
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
    v___x_6493_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6493_, 0, v___x_6492_);
    crate::leanh::lean_ctor_set(v___x_6493_, 1, v___f_6491_);
    crate::leanh::lean_ctor_set(v___x_6493_, 2, v___x_6490_);
    crate::leanh::lean_ctor_set(v___x_6493_, 3, v___f_6489_);
    crate::leanh::lean_ctor_set(v___x_6493_, 4, v___f_6488_);
    return v___x_6493_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt() -> *mut crate::leanh::LeanObject {
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5_once),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt___closed__5,
    );
    return v___x_6494_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6496_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt;
    v___x_6497_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_6496_);
    return v___x_6497_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2____boxed(
    mut v_a_6498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6499_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
    return v_res_6499_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6501_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0___closed__0;
    v___x_6502_ = l_Lean_stringToMessageData(v___x_6501_);
    return v___x_6502_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(
    mut v_____r_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
    mut v___y_6507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6509_ = crate::leanh::lean_obj_once(
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
    mut v_____r_6511_: *mut crate::leanh::LeanObject,
    mut v___y_6512_: *mut crate::leanh::LeanObject,
    mut v___y_6513_: *mut crate::leanh::LeanObject,
    mut v___y_6514_: *mut crate::leanh::LeanObject,
    mut v___y_6515_: *mut crate::leanh::LeanObject,
    mut v___y_6516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6517_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__0(
        v_____r_6511_,
        v___y_6512_,
        v___y_6513_,
        v___y_6514_,
        v___y_6515_,
    );
    crate::leanh::lean_dec(v___y_6515_);
    crate::leanh::lean_dec_ref(v___y_6514_);
    crate::leanh::lean_dec(v___y_6513_);
    crate::leanh::lean_dec_ref(v___y_6512_);
    return v_res_6517_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0()
-> f64 {
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: f64 = 0.0;
    v___x_6518_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6519_ = lean_float_of_nat(v___x_6518_);
    return v___x_6519_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(
    mut v_cls_6523_: *mut crate::leanh::LeanObject,
    mut v_msg_6524_: *mut crate::leanh::LeanObject,
    mut v___y_6525_: *mut crate::leanh::LeanObject,
    mut v___y_6526_: *mut crate::leanh::LeanObject,
    mut v___y_6527_: *mut crate::leanh::LeanObject,
    mut v___y_6528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6535_: u8 = 0;
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6548_: u8 = 0;
    let mut v_tid_6549_: u64 = 0;
    let mut v_traces_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6553_: u8 = 0;
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: f64 = 0.0;
    let mut v___x_6556_: u8 = 0;
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6574_: u8 = 0;
    let mut v_isSharedCheck_6575_: u8 = 0;
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6530_ = crate::leanh::lean_ctor_get(v___y_6527_, 5);
                v___x_6531_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__8(v_msg_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
                v_a_6532_ = crate::leanh::lean_ctor_get(v___x_6531_, 0);
                v_isSharedCheck_6576_ = (!crate::leanh::lean_is_exclusive(v___x_6531_)) as u8;
                if v_isSharedCheck_6576_ == 0 {
                    v___x_6534_ = v___x_6531_;
                    v_isShared_6535_ = v_isSharedCheck_6576_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6532_);
                    crate::leanh::lean_dec(v___x_6531_);
                    v___x_6534_ = crate::leanh::lean_box(0);
                    v_isShared_6535_ = v_isSharedCheck_6576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6536_ = lean_st_ref_take(v___y_6528_);
                v_traceState_6537_ = crate::leanh::lean_ctor_get(v___x_6536_, 4);
                v_env_6538_ = crate::leanh::lean_ctor_get(v___x_6536_, 0);
                v_nextMacroScope_6539_ = crate::leanh::lean_ctor_get(v___x_6536_, 1);
                v_ngen_6540_ = crate::leanh::lean_ctor_get(v___x_6536_, 2);
                v_auxDeclNGen_6541_ = crate::leanh::lean_ctor_get(v___x_6536_, 3);
                v_cache_6542_ = crate::leanh::lean_ctor_get(v___x_6536_, 5);
                v_messages_6543_ = crate::leanh::lean_ctor_get(v___x_6536_, 6);
                v_infoState_6544_ = crate::leanh::lean_ctor_get(v___x_6536_, 7);
                v_snapshotTasks_6545_ = crate::leanh::lean_ctor_get(v___x_6536_, 8);
                v_isSharedCheck_6575_ = (!crate::leanh::lean_is_exclusive(v___x_6536_)) as u8;
                if v_isSharedCheck_6575_ == 0 {
                    v___x_6547_ = v___x_6536_;
                    v_isShared_6548_ = v_isSharedCheck_6575_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6545_);
                    crate::leanh::lean_inc(v_infoState_6544_);
                    crate::leanh::lean_inc(v_messages_6543_);
                    crate::leanh::lean_inc(v_cache_6542_);
                    crate::leanh::lean_inc(v_traceState_6537_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6541_);
                    crate::leanh::lean_inc(v_ngen_6540_);
                    crate::leanh::lean_inc(v_nextMacroScope_6539_);
                    crate::leanh::lean_inc(v_env_6538_);
                    crate::leanh::lean_dec(v___x_6536_);
                    v___x_6547_ = crate::leanh::lean_box(0);
                    v_isShared_6548_ = v_isSharedCheck_6575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6549_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6537_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6550_ = crate::leanh::lean_ctor_get(v_traceState_6537_, 0);
                v_isSharedCheck_6574_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6537_)) as u8;
                if v_isSharedCheck_6574_ == 0 {
                    v___x_6552_ = v_traceState_6537_;
                    v_isShared_6553_ = v_isSharedCheck_6574_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_6550_);
                    crate::leanh::lean_dec(v_traceState_6537_);
                    v___x_6552_ = crate::leanh::lean_box(0);
                    v_isShared_6553_ = v_isSharedCheck_6574_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6554_ = crate::leanh::lean_box(0);
                v___x_6555_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__0);
                v___x_6556_ = 0;
                v___x_6557_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__1;
                v___x_6558_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_6558_, 0, v_cls_6523_);
                crate::leanh::lean_ctor_set(v___x_6558_, 1, v___x_6554_);
                crate::leanh::lean_ctor_set(v___x_6558_, 2, v___x_6557_);
                crate::leanh::lean_ctor_set_float(
                    v___x_6558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6555_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_6558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6555_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6556_,
                );
                v___x_6559_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1___closed__2;
                v___x_6560_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6560_, 0, v___x_6558_);
                crate::leanh::lean_ctor_set(v___x_6560_, 1, v_a_6532_);
                crate::leanh::lean_ctor_set(v___x_6560_, 2, v___x_6559_);
                crate::leanh::lean_inc(v_ref_6530_);
                v___x_6561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6561_, 0, v_ref_6530_);
                crate::leanh::lean_ctor_set(v___x_6561_, 1, v___x_6560_);
                v___x_6562_ = l_Lean_PersistentArray_push___redArg(v_traces_6550_, v___x_6561_);
                if v_isShared_6553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6552_, 0, v___x_6562_);
                    v___x_6564_ = v___x_6552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6573_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6573_, 0, v___x_6562_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6573_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6549_,
                    );
                    v___x_6564_ = v_reuseFailAlloc_6573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6547_, 4, v___x_6564_);
                    v___x_6566_ = v___x_6547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6572_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_env_6538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 1, v_nextMacroScope_6539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 2, v_ngen_6540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 3, v_auxDeclNGen_6541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 4, v___x_6564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 5, v_cache_6542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 6, v_messages_6543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 7, v_infoState_6544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 8, v_snapshotTasks_6545_);
                    v___x_6566_ = v_reuseFailAlloc_6572_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6567_ = lean_st_ref_set(v___y_6528_, v___x_6566_);
                v___x_6568_ = crate::leanh::lean_box(0);
                if v_isShared_6535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6534_, 0, v___x_6568_);
                    v___x_6570_ = v___x_6534_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 0, v___x_6568_);
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
    mut v_cls_6577_: *mut crate::leanh::LeanObject,
    mut v_msg_6578_: *mut crate::leanh::LeanObject,
    mut v___y_6579_: *mut crate::leanh::LeanObject,
    mut v___y_6580_: *mut crate::leanh::LeanObject,
    mut v___y_6581_: *mut crate::leanh::LeanObject,
    mut v___y_6582_: *mut crate::leanh::LeanObject,
    mut v___y_6583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6584_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(
        v_cls_6577_,
        v_msg_6578_,
        v___y_6579_,
        v___y_6580_,
        v___y_6581_,
        v___y_6582_,
    );
    crate::leanh::lean_dec(v___y_6582_);
    crate::leanh::lean_dec_ref(v___y_6581_);
    crate::leanh::lean_dec(v___y_6580_);
    crate::leanh::lean_dec_ref(v___y_6579_);
    return v_res_6584_;
}
pub unsafe fn l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(
    mut v_constName_6585_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_6586_: u8,
    mut v___y_6587_: *mut crate::leanh::LeanObject,
    mut v___y_6588_: *mut crate::leanh::LeanObject,
    mut v___y_6589_: *mut crate::leanh::LeanObject,
    mut v___y_6590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6592_ = lean_st_ref_get(v___y_6590_);
                v_env_6593_ = crate::leanh::lean_ctor_get(v___x_6592_, 0);
                crate::leanh::lean_inc_ref(v_env_6593_);
                crate::leanh::lean_dec(v___x_6592_);
                crate::leanh::lean_inc(v_constName_6585_);
                v___x_6594_ = l_Lean_Environment_findAsync_x3f(
                    v_env_6593_,
                    v_constName_6585_,
                    v_skipRealize_6586_,
                );
                if crate::leanh::lean_obj_tag(v___x_6594_) == 0 {
                    v___x_6595_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0___redArg(v_constName_6585_, v___y_6587_, v___y_6588_, v___y_6589_, v___y_6590_);
                    return v___x_6595_;
                } else {
                    crate::leanh::lean_dec(v_constName_6585_);
                    v_val_6596_ = crate::leanh::lean_ctor_get(v___x_6594_, 0);
                    v_isSharedCheck_6603_ = (!crate::leanh::lean_is_exclusive(v___x_6594_)) as u8;
                    if v_isSharedCheck_6603_ == 0 {
                        v___x_6598_ = v___x_6594_;
                        v_isShared_6599_ = v_isSharedCheck_6603_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6596_);
                        crate::leanh::lean_dec(v___x_6594_);
                        v___x_6598_ = crate::leanh::lean_box(0);
                        v_isShared_6599_ = v_isSharedCheck_6603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6599_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6598_, 0);
                    v___x_6601_ = v___x_6598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_val_6596_);
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
    mut v_constName_6604_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_6605_: *mut crate::leanh::LeanObject,
    mut v___y_6606_: *mut crate::leanh::LeanObject,
    mut v___y_6607_: *mut crate::leanh::LeanObject,
    mut v___y_6608_: *mut crate::leanh::LeanObject,
    mut v___y_6609_: *mut crate::leanh::LeanObject,
    mut v___y_6610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_6611_: u8 = 0;
    let mut v_res_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_6611_ = (crate::leanh::lean_unbox(v_skipRealize_6605_) as u8);
    v_res_6612_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(
        v_constName_6604_,
        v_skipRealize_boxed_6611_,
        v___y_6606_,
        v___y_6607_,
        v___y_6608_,
        v___y_6609_,
    );
    crate::leanh::lean_dec(v___y_6609_);
    crate::leanh::lean_dec_ref(v___y_6608_);
    crate::leanh::lean_dec(v___y_6607_);
    crate::leanh::lean_dec_ref(v___y_6606_);
    return v_res_6612_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1() -> u64 {
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: u64 = 0;
    v___x_6619_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0;
    v___x_6620_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6619_);
    return v___x_6620_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6621_: u64 = 0;
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6621_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__1,
    );
    v___x_6622_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__0;
    v___x_6623_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_6623_, 0, v___x_6622_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_6623_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_6621_,
    );
    return v___x_6623_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6624_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6624_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6625_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__3,
    );
    v___x_6626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6626_, 0, v___x_6625_);
    return v___x_6626_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6627_ = crate::leanh::lean_box(1);
    v___x_6628_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_6629_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6630_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6630_, 0, v___x_6629_);
    crate::leanh::lean_ctor_set(v___x_6630_, 1, v___x_6628_);
    crate::leanh::lean_ctor_set(v___x_6630_, 2, v___x_6627_);
    return v___x_6630_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6634_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6635_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6635_, 0, v___x_6634_);
    crate::leanh::lean_ctor_set(v___x_6635_, 1, v___x_6634_);
    crate::leanh::lean_ctor_set(v___x_6635_, 2, v___x_6634_);
    crate::leanh::lean_ctor_set(v___x_6635_, 3, v___x_6634_);
    crate::leanh::lean_ctor_set(v___x_6635_, 4, v___x_6633_);
    crate::leanh::lean_ctor_set(v___x_6635_, 5, v___x_6633_);
    crate::leanh::lean_ctor_set(v___x_6635_, 6, v___x_6633_);
    crate::leanh::lean_ctor_set(v___x_6635_, 7, v___x_6633_);
    crate::leanh::lean_ctor_set(v___x_6635_, 8, v___x_6633_);
    crate::leanh::lean_ctor_set(v___x_6635_, 9, v___x_6633_);
    return v___x_6635_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6636_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6637_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6637_, 0, v___x_6636_);
    crate::leanh::lean_ctor_set(v___x_6637_, 1, v___x_6636_);
    crate::leanh::lean_ctor_set(v___x_6637_, 2, v___x_6636_);
    crate::leanh::lean_ctor_set(v___x_6637_, 3, v___x_6636_);
    crate::leanh::lean_ctor_set(v___x_6637_, 4, v___x_6636_);
    crate::leanh::lean_ctor_set(v___x_6637_, 5, v___x_6636_);
    return v___x_6637_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__4,
    );
    v___x_6639_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6639_, 0, v___x_6638_);
    crate::leanh::lean_ctor_set(v___x_6639_, 1, v___x_6638_);
    crate::leanh::lean_ctor_set(v___x_6639_, 2, v___x_6638_);
    crate::leanh::lean_ctor_set(v___x_6639_, 3, v___x_6638_);
    crate::leanh::lean_ctor_set(v___x_6639_, 4, v___x_6638_);
    return v___x_6639_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6644_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__12;
    v___x_6645_ = l_Lean_stringToMessageData(v___x_6644_);
    return v___x_6645_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6646_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
    v___x_6647_ = l_String_toRawSubstring_x27(v___x_6646_);
    return v___x_6647_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6651_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_6651_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1(
    mut v___x_6654_: *mut crate::leanh::LeanObject,
    mut v_ext_6655_: *mut crate::leanh::LeanObject,
    mut v___f_6656_: *mut crate::leanh::LeanObject,
    mut v___x_6657_: *mut crate::leanh::LeanObject,
    mut v___x_6658_: *mut crate::leanh::LeanObject,
    mut v___x_6659_: *mut crate::leanh::LeanObject,
    mut v___x_6660_: *mut crate::leanh::LeanObject,
    mut v_declName_6661_: *mut crate::leanh::LeanObject,
    mut v_stx_6662_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6663_: u8,
    mut v___y_6664_: *mut crate::leanh::LeanObject,
    mut v___y_6665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6667_: u8 = 0;
    let mut v___x_6668_: u8 = 0;
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6688_: u8 = 0;
    let mut v___x_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6704_: u8 = 0;
    let mut v_hasTrace_6705_: u8 = 0;
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: u8 = 0;
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6720_: u8 = 0;
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_add_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6740_: u8 = 0;
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: u8 = 0;
    let mut v___x_6756_: u8 = 0;
    let mut v_reuseFailAlloc_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_unused_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v_ref_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6775_: u8 = 0;
    let mut v_isSharedCheck_6776_: u8 = 0;
    let mut v_unused_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: u8 = 0;
    let mut v___x_6779_: u8 = 0;
    let mut v_isSharedCheck_6780_: u8 = 0;
    let mut v_a_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6788_: u8 = 0;
    let mut v_a_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6792_: u8 = 0;
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6667_ = 0;
                v___x_6668_ = 1;
                v___x_6669_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__2,
                );
                v___x_6670_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
                v___x_6672_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__5,
                );
                v___x_6673_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__6;
                v___x_6674_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_6654_);
                v___x_6675_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_6675_, 0, v___x_6669_);
                crate::leanh::lean_ctor_set(v___x_6675_, 1, v___x_6654_);
                crate::leanh::lean_ctor_set(v___x_6675_, 2, v___x_6672_);
                crate::leanh::lean_ctor_set(v___x_6675_, 3, v___x_6673_);
                crate::leanh::lean_ctor_set(v___x_6675_, 4, v___x_6674_);
                crate::leanh::lean_ctor_set(v___x_6675_, 5, v___x_6670_);
                crate::leanh::lean_ctor_set(v___x_6675_, 6, v___x_6674_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_6667_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_6667_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_6667_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_6668_,
                );
                v___x_6676_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__7,
                );
                v___x_6677_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__8,
                );
                v___x_6678_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__9,
                );
                v___x_6679_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6679_, 0, v___x_6676_);
                crate::leanh::lean_ctor_set(v___x_6679_, 1, v___x_6677_);
                crate::leanh::lean_ctor_set(v___x_6679_, 2, v___x_6654_);
                crate::leanh::lean_ctor_set(v___x_6679_, 3, v___x_6671_);
                crate::leanh::lean_ctor_set(v___x_6679_, 4, v___x_6678_);
                v___x_6680_ = lean_st_mk_ref(v___x_6679_);
                crate::leanh::lean_inc(v_declName_6661_);
                v___x_6681_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__0(v_declName_6661_, v___x_6667_, v___x_6675_, v___x_6680_, v___y_6664_, v___y_6665_);
                if crate::leanh::lean_obj_tag(v___x_6681_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6681_, 1);
                    v___x_6682_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6683_ = l_Lean_Syntax_getArg(v_stx_6662_, v___x_6682_);
                    crate::leanh::lean_inc(v___x_6683_);
                    v___x_6684_ = l_Lean_getAttrParamOptPrio(v___x_6683_, v___y_6664_, v___y_6665_);
                    if crate::leanh::lean_obj_tag(v___x_6684_) == 0 {
                        v_a_6685_ = crate::leanh::lean_ctor_get(v___x_6684_, 0);
                        v_isSharedCheck_6780_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6684_)) as u8;
                        if v_isSharedCheck_6780_ == 0 {
                            v___x_6687_ = v___x_6684_;
                            v_isShared_6688_ = v_isSharedCheck_6780_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6685_);
                            crate::leanh::lean_dec(v___x_6684_);
                            v___x_6687_ = crate::leanh::lean_box(0);
                            v_isShared_6688_ = v_isSharedCheck_6780_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6683_);
                        crate::leanh::lean_dec(v___x_6680_);
                        crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                        crate::leanh::lean_dec(v_declName_6661_);
                        crate::leanh::lean_dec_ref(v___x_6660_);
                        crate::leanh::lean_dec_ref(v___x_6659_);
                        crate::leanh::lean_dec_ref(v___x_6658_);
                        crate::leanh::lean_dec_ref(v___x_6657_);
                        crate::leanh::lean_dec_ref(v___f_6656_);
                        crate::leanh::lean_dec_ref(v_ext_6655_);
                        v_a_6781_ = crate::leanh::lean_ctor_get(v___x_6684_, 0);
                        v_isSharedCheck_6788_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6684_)) as u8;
                        if v_isSharedCheck_6788_ == 0 {
                            v___x_6783_ = v___x_6684_;
                            v_isShared_6784_ = v_isSharedCheck_6788_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6781_);
                            crate::leanh::lean_dec(v___x_6684_);
                            v___x_6783_ = crate::leanh::lean_box(0);
                            v_isShared_6784_ = v_isSharedCheck_6788_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6680_);
                    crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                    crate::leanh::lean_dec(v_declName_6661_);
                    crate::leanh::lean_dec_ref(v___x_6660_);
                    crate::leanh::lean_dec_ref(v___x_6659_);
                    crate::leanh::lean_dec_ref(v___x_6658_);
                    crate::leanh::lean_dec_ref(v___x_6657_);
                    crate::leanh::lean_dec_ref(v___f_6656_);
                    crate::leanh::lean_dec_ref(v_ext_6655_);
                    v_a_6789_ = crate::leanh::lean_ctor_get(v___x_6681_, 0);
                    v_isSharedCheck_6796_ = (!crate::leanh::lean_is_exclusive(v___x_6681_)) as u8;
                    if v_isSharedCheck_6796_ == 0 {
                        v___x_6791_ = v___x_6681_;
                        v_isShared_6792_ = v_isSharedCheck_6796_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6789_);
                        crate::leanh::lean_dec(v___x_6681_);
                        v___x_6791_ = crate::leanh::lean_box(0);
                        v_isShared_6792_ = v_isSharedCheck_6796_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6689_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_declName_6661_);
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
                if crate::leanh::lean_obj_tag(v___x_6717_) == 0 {
                    crate::leanh::lean_dec(v___x_6683_);
                    crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                    crate::leanh::lean_dec(v_declName_6661_);
                    crate::leanh::lean_dec_ref(v___x_6660_);
                    crate::leanh::lean_dec_ref(v___x_6659_);
                    crate::leanh::lean_dec_ref(v___x_6658_);
                    crate::leanh::lean_dec_ref(v___x_6657_);
                    crate::leanh::lean_dec_ref(v___f_6656_);
                    v___y_6696_ = v___x_6717_;
                    state = 4;
                    continue;
                } else {
                    v_a_6718_ = crate::leanh::lean_ctor_get(v___x_6717_, 0);
                    crate::leanh::lean_inc(v_a_6718_);
                    v___x_6778_ = l_Lean_Exception_isInterrupt(v_a_6718_);
                    if v___x_6778_ == 0 {
                        v___x_6779_ = l_Lean_Exception_isRuntime(v_a_6718_);
                        v___y_6720_ = v___x_6779_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6718_);
                        v___y_6720_ = v___x_6778_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6691_ = lean_st_ref_get(v___x_6680_);
                crate::leanh::lean_dec(v___x_6680_);
                crate::leanh::lean_dec(v___x_6691_);
                if v_isShared_6688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6687_, 0, v___x_6689_);
                    v___x_6693_ = v___x_6687_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 0, v___x_6689_);
                    v___x_6693_ = v_reuseFailAlloc_6694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6693_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_6696_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_6696_, 1);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_6687_);
                    crate::leanh::lean_dec(v___x_6680_);
                    return v___y_6696_;
                }
            }
            5 => {
                crate::leanh::lean_inc(v___y_6665_);
                crate::leanh::lean_inc_ref(v___y_6664_);
                crate::leanh::lean_inc(v___x_6680_);
                v___x_6698_ = crate::leanh::lean_apply_6(
                    v___f_6656_,
                    v___x_6689_,
                    v___x_6675_,
                    v___x_6680_,
                    v___y_6664_,
                    v___y_6665_,
                    crate::leanh::lean_box(0),
                );
                v___y_6696_ = v___x_6698_;
                state = 4;
                continue;
            }
            6 => {
                if v___y_6704_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6702_);
                    v_hasTrace_6705_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6700_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6705_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_6701_);
                        crate::leanh::lean_dec_ref(v___x_6659_);
                        crate::leanh::lean_dec_ref(v___x_6658_);
                        crate::leanh::lean_dec_ref(v___x_6657_);
                        state = 5;
                        continue;
                    } else {
                        v___x_6706_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
                        v___x_6707_ =
                            l_Lean_Name_mkStr4(v___x_6657_, v___x_6658_, v___x_6659_, v___x_6706_);
                        v___x_6708_ =
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__11;
                        crate::leanh::lean_inc(v___x_6707_);
                        v___x_6709_ = l_Lean_Name_append(v___x_6708_, v___x_6707_);
                        v___x_6710_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___y_6703_,
                            v___y_6700_,
                            v___x_6709_,
                        );
                        crate::leanh::lean_dec(v___x_6709_);
                        if v___x_6710_ == 0 {
                            crate::leanh::lean_dec(v___x_6707_);
                            crate::leanh::lean_dec_ref(v___y_6701_);
                            state = 5;
                            continue;
                        } else {
                            v___x_6711_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__13);
                            v___x_6712_ = l_Lean_Exception_toMessageData(v___y_6701_);
                            v___x_6713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6713_, 0, v___x_6711_);
                            crate::leanh::lean_ctor_set(v___x_6713_, 1, v___x_6712_);
                            v___x_6714_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__1(v___x_6707_, v___x_6713_, v___x_6675_, v___x_6680_, v___y_6664_, v___y_6665_);
                            if crate::leanh::lean_obj_tag(v___x_6714_) == 0 {
                                v_a_6715_ = crate::leanh::lean_ctor_get(v___x_6714_, 0);
                                crate::leanh::lean_inc(v_a_6715_);
                                crate::leanh::lean_dec_ref_known(v___x_6714_, 1);
                                crate::leanh::lean_inc(v___y_6665_);
                                crate::leanh::lean_inc_ref(v___y_6664_);
                                crate::leanh::lean_inc(v___x_6680_);
                                v___x_6716_ = crate::leanh::lean_apply_6(
                                    v___f_6656_,
                                    v_a_6715_,
                                    v___x_6675_,
                                    v___x_6680_,
                                    v___y_6664_,
                                    v___y_6665_,
                                    crate::leanh::lean_box(0),
                                );
                                v___y_6696_ = v___x_6716_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                                crate::leanh::lean_dec_ref(v___f_6656_);
                                v___y_6696_ = v___x_6714_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6701_);
                    crate::leanh::lean_del_object(v___x_6687_);
                    crate::leanh::lean_dec(v___x_6680_);
                    crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                    crate::leanh::lean_dec_ref(v___x_6659_);
                    crate::leanh::lean_dec_ref(v___x_6658_);
                    crate::leanh::lean_dec_ref(v___x_6657_);
                    crate::leanh::lean_dec_ref(v___f_6656_);
                    return v___y_6702_;
                }
            }
            7 => {
                if v___y_6720_ == 0 {
                    v_isSharedCheck_6776_ = (!crate::leanh::lean_is_exclusive(v___x_6717_)) as u8;
                    if v_isSharedCheck_6776_ == 0 {
                        v_unused_6777_ = crate::leanh::lean_ctor_get(v___x_6717_, 0);
                        crate::leanh::lean_dec(v_unused_6777_);
                        v___x_6722_ = v___x_6717_;
                        v_isShared_6723_ = v_isSharedCheck_6776_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6717_);
                        v___x_6722_ = crate::leanh::lean_box(0);
                        v_isShared_6723_ = v_isSharedCheck_6776_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6683_);
                    crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                    crate::leanh::lean_dec(v_declName_6661_);
                    crate::leanh::lean_dec_ref(v___x_6660_);
                    crate::leanh::lean_dec_ref(v___x_6659_);
                    crate::leanh::lean_dec_ref(v___x_6658_);
                    crate::leanh::lean_dec_ref(v___x_6657_);
                    crate::leanh::lean_dec_ref(v___f_6656_);
                    v___y_6696_ = v___x_6717_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_6724_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_;
                v___x_6725_ = l_Lean_getBuiltinAttributeImpl(v___x_6724_);
                if crate::leanh::lean_obj_tag(v___x_6725_) == 0 {
                    crate::leanh::lean_del_object(v___x_6722_);
                    v_a_6726_ = crate::leanh::lean_ctor_get(v___x_6725_, 0);
                    crate::leanh::lean_inc(v_a_6726_);
                    crate::leanh::lean_dec_ref_known(v___x_6725_, 1);
                    v_options_6727_ = crate::leanh::lean_ctor_get(v___y_6664_, 2);
                    v_ref_6728_ = crate::leanh::lean_ctor_get(v___y_6664_, 5);
                    v_quotContext_6729_ = crate::leanh::lean_ctor_get(v___y_6664_, 10);
                    v_currMacroScope_6730_ = crate::leanh::lean_ctor_get(v___y_6664_, 11);
                    v_inheritedTraceOptions_6731_ = crate::leanh::lean_ctor_get(v___y_6664_, 13);
                    v___x_6732_ = l_Lean_SourceInfo_fromRef(v_ref_6728_, v___y_6720_);
                    v___x_6733_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__14,
                    );
                    crate::leanh::lean_inc(v_currMacroScope_6730_);
                    crate::leanh::lean_inc(v_quotContext_6729_);
                    v___x_6734_ = l_Lean_addMacroScope(
                        v_quotContext_6729_,
                        v___x_6724_,
                        v_currMacroScope_6730_,
                    );
                    v___x_6735_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_6732_);
                    v___x_6736_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6736_, 0, v___x_6732_);
                    crate::leanh::lean_ctor_set(v___x_6736_, 1, v___x_6733_);
                    crate::leanh::lean_ctor_set(v___x_6736_, 2, v___x_6734_);
                    crate::leanh::lean_ctor_set(v___x_6736_, 3, v___x_6735_);
                    v_add_6737_ = crate::leanh::lean_ctor_get(v_a_6726_, 1);
                    v_isSharedCheck_6758_ = (!crate::leanh::lean_is_exclusive(v_a_6726_)) as u8;
                    if v_isSharedCheck_6758_ == 0 {
                        v_unused_6759_ = crate::leanh::lean_ctor_get(v_a_6726_, 2);
                        crate::leanh::lean_dec(v_unused_6759_);
                        v_unused_6760_ = crate::leanh::lean_ctor_get(v_a_6726_, 0);
                        crate::leanh::lean_dec(v_unused_6760_);
                        v___x_6739_ = v_a_6726_;
                        v_isShared_6740_ = v_isSharedCheck_6758_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_add_6737_);
                        crate::leanh::lean_dec(v_a_6726_);
                        v___x_6739_ = crate::leanh::lean_box(0);
                        v_isShared_6740_ = v_isSharedCheck_6758_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6687_);
                    crate::leanh::lean_dec(v___x_6683_);
                    crate::leanh::lean_dec(v___x_6680_);
                    crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                    crate::leanh::lean_dec(v_declName_6661_);
                    crate::leanh::lean_dec_ref(v___x_6660_);
                    crate::leanh::lean_dec_ref(v___x_6659_);
                    crate::leanh::lean_dec_ref(v___x_6658_);
                    crate::leanh::lean_dec_ref(v___x_6657_);
                    crate::leanh::lean_dec_ref(v___f_6656_);
                    v_a_6761_ = crate::leanh::lean_ctor_get(v___x_6725_, 0);
                    v_isSharedCheck_6775_ = (!crate::leanh::lean_is_exclusive(v___x_6725_)) as u8;
                    if v_isSharedCheck_6775_ == 0 {
                        v___x_6763_ = v___x_6725_;
                        v_isShared_6764_ = v_isSharedCheck_6775_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6761_);
                        crate::leanh::lean_dec(v___x_6725_);
                        v___x_6763_ = crate::leanh::lean_box(0);
                        v_isShared_6764_ = v_isSharedCheck_6775_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_6741_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__16;
                v___x_6742_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___closed__17,
                );
                crate::leanh::lean_inc(v___x_6732_);
                if v_isShared_6740_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6739_, 1);
                    crate::leanh::lean_ctor_set(v___x_6739_, 2, v___x_6742_);
                    crate::leanh::lean_ctor_set(v___x_6739_, 1, v___x_6741_);
                    crate::leanh::lean_ctor_set(v___x_6739_, 0, v___x_6732_);
                    v___x_6744_ = v___x_6739_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 0, v___x_6732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 1, v___x_6741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6757_, 2, v___x_6742_);
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
                v___x_6750_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6751_ = l_Lean_Syntax_setArg(v___x_6749_, v___x_6750_, v___x_6683_);
                v___x_6752_ = crate::leanh::lean_box((v_attrKind_6663_) as usize);
                crate::leanh::lean_inc(v___y_6665_);
                crate::leanh::lean_inc_ref(v___y_6664_);
                v___x_6753_ = crate::leanh::lean_apply_6(
                    v_add_6737_,
                    v_declName_6661_,
                    v___x_6751_,
                    v___x_6752_,
                    v___y_6664_,
                    v___y_6665_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6753_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6753_, 1);
                    crate::leanh::lean_dec_ref_known(v___x_6675_, 7);
                    crate::leanh::lean_dec_ref(v___x_6659_);
                    crate::leanh::lean_dec_ref(v___x_6658_);
                    crate::leanh::lean_dec_ref(v___x_6657_);
                    crate::leanh::lean_dec_ref(v___f_6656_);
                    state = 2;
                    continue;
                } else {
                    v_a_6754_ = crate::leanh::lean_ctor_get(v___x_6753_, 0);
                    crate::leanh::lean_inc(v_a_6754_);
                    v___x_6755_ = l_Lean_Exception_isInterrupt(v_a_6754_);
                    if v___x_6755_ == 0 {
                        crate::leanh::lean_inc(v_a_6754_);
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
                v_ref_6765_ = crate::leanh::lean_ctor_get(v___y_6664_, 5);
                v___x_6766_ = lean_io_error_to_string(v_a_6761_);
                if v_isShared_6723_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6722_, 3);
                    crate::leanh::lean_ctor_set(v___x_6722_, 0, v___x_6766_);
                    v___x_6768_ = v___x_6722_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6774_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6774_, 0, v___x_6766_);
                    v___x_6768_ = v_reuseFailAlloc_6774_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6769_ = l_Lean_MessageData_ofFormat(v___x_6768_);
                crate::leanh::lean_inc(v_ref_6765_);
                v___x_6770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6770_, 0, v_ref_6765_);
                crate::leanh::lean_ctor_set(v___x_6770_, 1, v___x_6769_);
                if v_isShared_6764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6763_, 0, v___x_6770_);
                    v___x_6772_ = v___x_6763_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 0, v___x_6770_);
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
                    v_reuseFailAlloc_6787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6787_, 0, v_a_6781_);
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
                    v_reuseFailAlloc_6795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6795_, 0, v_a_6789_);
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
    mut v___x_6797_: *mut crate::leanh::LeanObject,
    mut v_ext_6798_: *mut crate::leanh::LeanObject,
    mut v___f_6799_: *mut crate::leanh::LeanObject,
    mut v___x_6800_: *mut crate::leanh::LeanObject,
    mut v___x_6801_: *mut crate::leanh::LeanObject,
    mut v___x_6802_: *mut crate::leanh::LeanObject,
    mut v___x_6803_: *mut crate::leanh::LeanObject,
    mut v_declName_6804_: *mut crate::leanh::LeanObject,
    mut v_stx_6805_: *mut crate::leanh::LeanObject,
    mut v_attrKind_6806_: *mut crate::leanh::LeanObject,
    mut v___y_6807_: *mut crate::leanh::LeanObject,
    mut v___y_6808_: *mut crate::leanh::LeanObject,
    mut v___y_6809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_6810_: u8 = 0;
    let mut v_res_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6810_ = (crate::leanh::lean_unbox(v_attrKind_6806_) as u8);
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
    crate::leanh::lean_dec(v___y_6808_);
    crate::leanh::lean_dec_ref(v___y_6807_);
    crate::leanh::lean_dec(v_stx_6805_);
    return v_res_6811_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(
    mut v_msgData_6812_: *mut crate::leanh::LeanObject,
    mut v___y_6813_: *mut crate::leanh::LeanObject,
    mut v___y_6814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6816_ = lean_st_ref_get(v___y_6814_);
    v_env_6817_ = crate::leanh::lean_ctor_get(v___x_6816_, 0);
    crate::leanh::lean_inc_ref(v_env_6817_);
    crate::leanh::lean_dec(v___x_6816_);
    v_options_6818_ = crate::leanh::lean_ctor_get(v___y_6813_, 2);
    v___x_6819_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
    v___x_6820_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6821_ = lean_mk_empty_array_with_capacity(v___x_6820_);
    crate::leanh::lean_dec_ref(v___x_6821_);
    v___x_6822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_6818_);
    v___x_6823_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6823_, 0, v_env_6817_);
    crate::leanh::lean_ctor_set(v___x_6823_, 1, v___x_6819_);
    crate::leanh::lean_ctor_set(v___x_6823_, 2, v___x_6822_);
    crate::leanh::lean_ctor_set(v___x_6823_, 3, v_options_6818_);
    v___x_6824_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6824_, 0, v___x_6823_);
    crate::leanh::lean_ctor_set(v___x_6824_, 1, v_msgData_6812_);
    v___x_6825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6825_, 0, v___x_6824_);
    return v___x_6825_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2___boxed(
    mut v_msgData_6826_: *mut crate::leanh::LeanObject,
    mut v___y_6827_: *mut crate::leanh::LeanObject,
    mut v___y_6828_: *mut crate::leanh::LeanObject,
    mut v___y_6829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6830_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msgData_6826_, v___y_6827_, v___y_6828_);
    crate::leanh::lean_dec(v___y_6828_);
    crate::leanh::lean_dec_ref(v___y_6827_);
    return v_res_6830_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
    mut v_msg_6831_: *mut crate::leanh::LeanObject,
    mut v___y_6832_: *mut crate::leanh::LeanObject,
    mut v___y_6833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6840_: u8 = 0;
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6835_ = crate::leanh::lean_ctor_get(v___y_6832_, 5);
                v___x_6836_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2_spec__2(v_msg_6831_, v___y_6832_, v___y_6833_);
                v_a_6837_ = crate::leanh::lean_ctor_get(v___x_6836_, 0);
                v_isSharedCheck_6845_ = (!crate::leanh::lean_is_exclusive(v___x_6836_)) as u8;
                if v_isSharedCheck_6845_ == 0 {
                    v___x_6839_ = v___x_6836_;
                    v_isShared_6840_ = v_isSharedCheck_6845_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6837_);
                    crate::leanh::lean_dec(v___x_6836_);
                    v___x_6839_ = crate::leanh::lean_box(0);
                    v_isShared_6840_ = v_isSharedCheck_6845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_6835_);
                v___x_6841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6841_, 0, v_ref_6835_);
                crate::leanh::lean_ctor_set(v___x_6841_, 1, v_a_6837_);
                if v_isShared_6840_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6839_, 1);
                    crate::leanh::lean_ctor_set(v___x_6839_, 0, v___x_6841_);
                    v___x_6843_ = v___x_6839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 0, v___x_6841_);
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
    mut v_msg_6846_: *mut crate::leanh::LeanObject,
    mut v___y_6847_: *mut crate::leanh::LeanObject,
    mut v___y_6848_: *mut crate::leanh::LeanObject,
    mut v___y_6849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6850_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
            v_msg_6846_,
            v___y_6847_,
            v___y_6848_,
        );
    crate::leanh::lean_dec(v___y_6848_);
    crate::leanh::lean_dec_ref(v___y_6847_);
    return v_res_6850_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6852_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__0;
    v___x_6853_ = l_Lean_stringToMessageData(v___x_6852_);
    return v___x_6853_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6855_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__2;
    v___x_6856_ = l_Lean_stringToMessageData(v___x_6855_);
    return v___x_6856_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(
    mut v___x_6857_: *mut crate::leanh::LeanObject,
    mut v_decl_6858_: *mut crate::leanh::LeanObject,
    mut v___y_6859_: *mut crate::leanh::LeanObject,
    mut v___y_6860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6862_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__1,
    );
    v___x_6863_ = l_Lean_MessageData_ofName(v___x_6857_);
    v___x_6864_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6864_, 0, v___x_6862_);
    crate::leanh::lean_ctor_set(v___x_6864_, 1, v___x_6863_);
    v___x_6865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___closed__3,
    );
    v___x_6866_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6866_, 0, v___x_6864_);
    crate::leanh::lean_ctor_set(v___x_6866_, 1, v___x_6865_);
    v___x_6867_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
            v___x_6866_,
            v___y_6859_,
            v___y_6860_,
        );
    return v___x_6867_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2___boxed(
    mut v___x_6868_: *mut crate::leanh::LeanObject,
    mut v_decl_6869_: *mut crate::leanh::LeanObject,
    mut v___y_6870_: *mut crate::leanh::LeanObject,
    mut v___y_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6873_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__2(
        v___x_6868_,
        v_decl_6869_,
        v___y_6870_,
        v___y_6871_,
    );
    crate::leanh::lean_dec(v___y_6871_);
    crate::leanh::lean_dec_ref(v___y_6870_);
    crate::leanh::lean_dec(v_decl_6869_);
    return v_res_6873_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(
    mut v_ext_6894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6895_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__0;
    v___x_6896_ = crate::leanh::lean_box(1);
    v___x_6897_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_6898_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_6899_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___x_6900_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_;
    v___f_6901_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___lam__1___boxed as *mut core::ffi::c_void,
        13,
        7,
    );
    crate::leanh::lean_closure_set(v___f_6901_, 0, v___x_6896_);
    crate::leanh::lean_closure_set(v___f_6901_, 1, v_ext_6894_);
    crate::leanh::lean_closure_set(v___f_6901_, 2, v___f_6895_);
    crate::leanh::lean_closure_set(v___f_6901_, 3, v___x_6898_);
    crate::leanh::lean_closure_set(v___f_6901_, 4, v___x_6899_);
    crate::leanh::lean_closure_set(v___f_6901_, 5, v___x_6900_);
    crate::leanh::lean_closure_set(v___f_6901_, 6, v___x_6897_);
    v___f_6902_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__5;
    v___x_6903_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr___closed__7;
    v___x_6904_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6904_, 0, v___x_6903_);
    crate::leanh::lean_ctor_set(v___x_6904_, 1, v___f_6901_);
    crate::leanh::lean_ctor_set(v___x_6904_, 2, v___f_6902_);
    return v___x_6904_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(
    mut v_00_u03b1_6905_: *mut crate::leanh::LeanObject,
    mut v_msg_6906_: *mut crate::leanh::LeanObject,
    mut v___y_6907_: *mut crate::leanh::LeanObject,
    mut v___y_6908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6910_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___redArg(
            v_msg_6906_,
            v___y_6907_,
            v___y_6908_,
        );
    return v___x_6910_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2___boxed(
    mut v_00_u03b1_6911_: *mut crate::leanh::LeanObject,
    mut v_msg_6912_: *mut crate::leanh::LeanObject,
    mut v___y_6913_: *mut crate::leanh::LeanObject,
    mut v___y_6914_: *mut crate::leanh::LeanObject,
    mut v___y_6915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6916_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr_spec__2(
        v_00_u03b1_6911_,
        v_msg_6912_,
        v___y_6913_,
        v___y_6914_,
    );
    crate::leanh::lean_dec(v___y_6914_);
    crate::leanh::lean_dec_ref(v___y_6913_);
    return v_res_6916_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6917_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
    v___x_6918_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecAttr(v___x_6917_);
    return v___x_6918_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6920_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_);
    v___x_6921_ = l_Lean_registerBuiltinAttribute(v___x_6920_);
    return v___x_6921_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2____boxed(
    mut v_a_6922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6923_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
    return v_res_6923_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(
    mut v_ext_6924_: *mut crate::leanh::LeanObject,
    mut v_a_6925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6927_ = lean_st_ref_get(v_a_6925_);
    v_ext_6928_ = crate::leanh::lean_ctor_get(v_ext_6924_, 1);
    v_toEnvExtension_6929_ = crate::leanh::lean_ctor_get(v_ext_6928_, 0);
    v_env_6930_ = crate::leanh::lean_ctor_get(v___x_6927_, 0);
    crate::leanh::lean_inc_ref(v_env_6930_);
    crate::leanh::lean_dec(v___x_6927_);
    v_asyncMode_6931_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6929_, 2);
    v___x_6932_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default;
    v___x_6933_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_6932_,
        v_ext_6924_,
        v_env_6930_,
        v_asyncMode_6931_,
    );
    v___x_6934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6934_, 0, v___x_6933_);
    return v___x_6934_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg___boxed(
    mut v_ext_6935_: *mut crate::leanh::LeanObject,
    mut v_a_6936_: *mut crate::leanh::LeanObject,
    mut v_a_6937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6938_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_6935_, v_a_6936_);
    crate::leanh::lean_dec(v_a_6936_);
    crate::leanh::lean_dec_ref(v_ext_6935_);
    return v_res_6938_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(
    mut v_ext_6939_: *mut crate::leanh::LeanObject,
    mut v_a_6940_: *mut crate::leanh::LeanObject,
    mut v_a_6941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6943_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v_ext_6939_, v_a_6941_);
    return v___x_6943_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___boxed(
    mut v_ext_6944_: *mut crate::leanh::LeanObject,
    mut v_a_6945_: *mut crate::leanh::LeanObject,
    mut v_a_6946_: *mut crate::leanh::LeanObject,
    mut v_a_6947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6948_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems(v_ext_6944_, v_a_6945_, v_a_6946_);
    crate::leanh::lean_dec(v_a_6946_);
    crate::leanh::lean_dec_ref(v_a_6945_);
    crate::leanh::lean_dec_ref(v_ext_6944_);
    return v_res_6948_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(
    mut v_a_6949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6951_ = l_Lean_Elab_Tactic_Do_SpecAttr_specAttr;
    v___x_6952_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecExtension_getTheorems___redArg(v___x_6951_, v_a_6949_);
    return v___x_6952_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg___boxed(
    mut v_a_6953_: *mut crate::leanh::LeanObject,
    mut v_a_6954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6955_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_6953_);
    crate::leanh::lean_dec(v_a_6953_);
    return v_res_6955_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(
    mut v_a_6956_: *mut crate::leanh::LeanObject,
    mut v_a_6957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6959_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_6957_);
    return v___x_6959_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___boxed(
    mut v_a_6960_: *mut crate::leanh::LeanObject,
    mut v_a_6961_: *mut crate::leanh::LeanObject,
    mut v_a_6962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6963_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems(v_a_6960_, v_a_6961_);
    crate::leanh::lean_dec(v_a_6961_);
    crate::leanh::lean_dec_ref(v_a_6960_);
    return v_res_6963_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(
    mut v_x_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6968_ = crate::leanh::lean_box(0);
    v___x_6969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6969_, 0, v___x_6968_);
    return v___x_6969_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2____boxed(
    mut v_x_6970_: *mut crate::leanh::LeanObject,
    mut v___y_6971_: *mut crate::leanh::LeanObject,
    mut v___y_6972_: *mut crate::leanh::LeanObject,
    mut v___y_6973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6974_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_(v_x_6970_, v___y_6971_, v___y_6972_);
    crate::leanh::lean_dec(v___y_6972_);
    crate::leanh::lean_dec_ref(v___y_6971_);
    crate::leanh::lean_dec(v_x_6970_);
    return v_res_6974_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: u8 = 0;
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6989_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6990_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6991_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6992_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_;
    v___x_6993_ = 0;
    v___x_6994_ = crate::leanh::lean_box(2);
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
    mut v_a_6996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6997_ = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
    return v_res_6997_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(
    mut v_env_6998_: *mut crate::leanh::LeanObject,
    mut v_ty_6999_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7000_ = l_Lean_Expr_getAppFn(v_ty_6999_);
    if crate::leanh::lean_obj_tag(v___x_7000_) == 4 {
        let mut v_declName_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7003_: u8 = 0;
        v_declName_7001_ = crate::leanh::lean_ctor_get(v___x_7000_, 0);
        crate::leanh::lean_inc(v_declName_7001_);
        crate::leanh::lean_dec_ref_known(v___x_7000_, 2);
        v___x_7002_ = l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr;
        v___x_7003_ = l_Lean_TagAttribute_hasTag(v___x_7002_, v_env_6998_, v_declName_7001_);
        return v___x_7003_;
    } else {
        let mut v___x_7004_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_7000_);
        crate::leanh::lean_dec_ref(v_env_6998_);
        v___x_7004_ = 0;
        return v___x_7004_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType___boxed(
    mut v_env_7005_: *mut crate::leanh::LeanObject,
    mut v_ty_7006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7007_: u8 = 0;
    let mut v_r_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7007_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_7005_, v_ty_7006_);
    crate::leanh::lean_dec_ref(v_ty_7006_);
    v_r_7008_ = crate::leanh::lean_box((v_res_7007_) as usize);
    return v_r_7008_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Attr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1315642830____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_3373485604____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mvcgenSimpExt);
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem_default,
    );
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorem);
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems_default,
    );
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheorems);
    l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_simpSPredConfig);
    l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt = _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecExt);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_1654486625____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Do_SpecAttr_specAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_2279960745____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Attr_0__Lean_Elab_Tactic_Do_SpecAttr_initFn_00___x40_Lean_Elab_Tactic_Do_Attr_545748732____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_specInvariantAttr);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Attr(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Attr(builtin);
}
