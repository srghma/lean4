// Lean compiler output
// Module: Lean.Meta.Coe
// Imports: Lean.Meta.AppBuilder Lean.ExtraModUses Lean.Meta.WHNF
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lean::Attributes::{l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Exception_isRuntime, l_Lean_mkArrow,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_const___override,
    l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArgD, l_Lean_Expr_hasMVar, l_Lean_Expr_headBeta, l_Lean_Expr_isConst,
    l_Lean_Expr_isForall, l_Lean_Expr_isSort, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq,
    l_Lean_ExprStructEq_hash, l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkBVar,
    l_Lean_mkConst, l_Lean_mkForall, l_Lean_mkSort,
};
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hint_x27, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_isMonad_x3f, l_Lean_Meta_mkAppOptM,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq, l_Lean_Meta_isLevelDefEq,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkFreshLevelMVar,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars, l_Lean_Meta_saveState___redArg,
    l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::DecLevel::{l_Lean_Meta_decLevel, l_Lean_Meta_getDecLevel};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_trySynthInstance;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_getProjectionFnInfo_x3f;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate_rev;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 101, 95, 100, 101, 99, 108, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4669255323461933537 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 40, 117, 110, 102, 111, 108, 100, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 41, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 101, 68, 101, 99, 108, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11032260531262264430 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<308> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 308, m_capacity: 308, m_length: 307, m_data: [84, 97, 103, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 116, 111, 32, 98, 101, 32, 117, 110, 102, 111, 108, 100, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 101, 108, 97, 98, 111, 114, 97, 116, 105, 111, 110, 46, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 109, 111, 115, 116, 108, 121, 32, 117, 115, 101, 100, 32, 116, 111, 32, 104, 105, 100, 101, 32, 99, 111, 101, 114, 99, 105, 111, 110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 100, 101, 116, 97, 105, 108, 115, 32, 97, 110, 100, 32, 115, 104, 111, 119, 32, 116, 104, 101, 32, 99, 111, 101, 114, 99, 101, 100, 32, 114, 101, 115, 117, 108, 116, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 10, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 40, 101, 46, 103, 46, 32, 96, 67, 111, 101, 84, 46, 99, 111, 101, 96, 44, 32, 96, 67, 111, 101, 46, 99, 111, 101, 96, 41, 46, 32, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 111, 110, 108, 121, 32, 119, 111, 114, 107, 115, 32, 111, 110, 10, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 115, 46, 10, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 112 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 112 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__7_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__14_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_expandCoe___lam__1___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_expandCoe___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_expandCoe___lam__1___closed__1_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [67, 111, 101, 0],
    };
static mut l_Lean_Meta_expandCoe___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_expandCoe___lam__1___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [99, 111, 101, 0],
    };
static mut l_Lean_Meta_expandCoe___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_expandCoe___lam__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16059047048258275031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_expandCoe___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16826351986644441918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_expandCoe___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_expandCoe___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_expandCoe___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_expandCoe___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_expandCoe___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_expandCoe___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_expandCoe___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_expandCoe___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_expandCoe___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_expandCoe___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_expandCoe___closed__2: u64 = 0;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 117, 116, 111, 76, 105, 102, 116, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6337689538456143528 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 64, m_capacity: 64, m_length: 63, m_data: [73, 110, 115, 101, 114, 116, 32, 109, 111, 110, 97, 100, 105, 99, 32, 108, 105, 102, 116, 115, 32, 40, 105, 46, 101, 46, 44, 32, 96, 108, 105, 102, 116, 77, 96, 32, 97, 110, 100, 32, 99, 111, 101, 114, 99, 105, 111, 110, 115, 41, 32, 119, 104, 101, 110, 32, 110, 101, 101, 100, 101, 100, 46, 0]};
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13662060717734213829 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value:
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
    m_data: [67, 111, 101, 84, 0],
};
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6065747394011725968 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6065747394011725968 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5620214693665263637 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3_value:
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
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 99, 111, 101, 114, 99, 101, 0,
    ],
};
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [10, 116, 111, 0],
};
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        10, 99, 111, 101, 114, 99, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110,
        32, 104, 97, 115, 32, 119, 114, 111, 110, 103, 32, 116, 121, 112, 101, 58, 0,
    ],
};
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceToFunction_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [67, 111, 101, 70, 117, 110, 0],
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceToFunction_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16258489208949799392 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_coerceToFunction_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16258489208949799392 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_coerceToFunction_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8017842707515137605 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceToFunction_x3f___closed__3_value: crate::leanh::LeanStringObject<17> =
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
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 101, 114, 99, 101, 0,
        ],
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceToFunction_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceToFunction_x3f___closed__5_value: crate::leanh::LeanStringObject<76> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 76,
        m_capacity: 76,
        m_length: 75,
        m_data: [
            10, 116, 111, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 58, 32, 65, 102, 116,
            101, 114, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 96, 67, 111, 101, 70, 117,
            110, 46, 99, 111, 101, 96, 44, 32, 114, 101, 115, 117, 108, 116, 32, 105, 115, 32, 115,
            116, 105, 108, 108, 32, 110, 111, 116, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111,
            110, 0,
        ],
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceToFunction_x3f___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceToFunction_x3f___closed__7_value: crate::leanh::LeanStringObject<80> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 80,
        m_capacity: 80,
        m_length: 79,
        m_data: [
            84, 104, 105, 115, 32, 105, 115, 32, 111, 102, 116, 101, 110, 32, 100, 117, 101, 32,
            116, 111, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 96, 67, 111, 101, 70, 117,
            110, 96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 59, 32, 116, 104, 101, 32, 115,
            121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99,
            101, 32, 119, 97, 115, 0,
        ],
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToFunction_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceToFunction_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceToFunction_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceToSort_x3f___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 101, 83, 111, 114, 116, 0],
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceToSort_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16015375085723986372 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_coerceToSort_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16015375085723986372 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_coerceToSort_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_expandCoe___lam__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17744461754681147897 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceToSort_x3f___closed__3_value: crate::leanh::LeanStringObject<69> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 69,
        m_capacity: 69,
        m_length: 68,
        m_data: [
            10, 116, 111, 32, 97, 32, 116, 121, 112, 101, 58, 32, 65, 102, 116, 101, 114, 32, 97,
            112, 112, 108, 121, 105, 110, 103, 32, 96, 67, 111, 101, 83, 111, 114, 116, 46, 99,
            111, 101, 96, 44, 32, 114, 101, 115, 117, 108, 116, 32, 105, 115, 32, 115, 116, 105,
            108, 108, 32, 110, 111, 116, 32, 97, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceToSort_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceToSort_x3f___closed__5_value: crate::leanh::LeanStringObject<81> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 81,
        m_capacity: 81,
        m_length: 80,
        m_data: [
            84, 104, 105, 115, 32, 105, 115, 32, 111, 102, 116, 101, 110, 32, 100, 117, 101, 32,
            116, 111, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 96, 67, 111, 101, 83, 111,
            114, 116, 96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 59, 32, 116, 104, 101, 32,
            115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110,
            99, 101, 32, 119, 97, 115, 0,
        ],
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceToSort_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceToSort_x3f___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceToSort_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_isTypeApp_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_isTypeApp_x3f___closed__0: u64 = 0;
pub static l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0_value:
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
static mut l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [77, 111, 110, 97, 100, 76, 105, 102, 116, 84, 0],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7572758637483522028 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [108, 105, 102, 116, 77, 0],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__2_value)
                as *mut crate::leanh::LeanObject,
            6561752574405000550 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [97, 0],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__4_value)
                as *mut crate::leanh::LeanObject,
            7839396180116328695 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__7_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__8_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 105, 102, 116, 67, 111, 101, 77, 0],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__7_value)
                as *mut crate::leanh::LeanObject,
            14216883915201854279 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__8_value)
                as *mut crate::leanh::LeanObject,
            3425639947135427131 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__10_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 111, 101, 77, 0],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__7_value)
                as *mut crate::leanh::LeanObject,
            14216883915201854279 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_coerceMonadLift_x3f___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__10_value)
                as *mut crate::leanh::LeanObject,
            8254521676566458133 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_coerceMonadLift_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_coerceMonadLift_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(
    mut v_x_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3964_ = crate::leanh::lean_box(0);
    v___x_3965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3964_);
    return v___x_3965_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(
    mut v_x_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_(v_x_3966_, v___y_3967_, v___y_3968_);
    crate::leanh::lean_dec(v___y_3968_);
    crate::leanh::lean_dec_ref(v___y_3967_);
    crate::leanh::lean_dec(v_x_3966_);
    return v_res_3970_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: u8 = 0;
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3984_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_;
    v___x_3985_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_;
    v___x_3986_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_;
    v___x_3987_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_;
    v___x_3988_ = 0;
    v___x_3989_ = crate::leanh::lean_box(2);
    v___x_3990_ = l_Lean_registerTagAttribute(
        v___x_3985_,
        v___x_3986_,
        v___f_3984_,
        v___x_3987_,
        v___x_3988_,
        v___x_3989_,
    );
    return v___x_3990_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2____boxed(
    mut v_a_3991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3992_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
    return v_res_3992_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3995_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_;
    v___x_3996_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___closed__0;
    v___x_3997_ = l_Lean_addBuiltinDocString(v___x_3995_, v___x_3996_);
    return v___x_3997_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1___boxed(
    mut v_a_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
    return v_res_3999_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4026_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_;
    v___x_4027_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___closed__6;
    v___x_4028_ = l_Lean_addBuiltinDeclarationRanges(v___x_4026_, v___x_4027_);
    return v___x_4028_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3___boxed(
    mut v_a_4029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4030_ = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
    return v_res_4030_;
}
pub unsafe fn l_Lean_Meta_isCoeDecl(
    mut v_env_4031_: *mut crate::leanh::LeanObject,
    mut v_declName_4032_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    v___x_4033_ = l_Lean_Meta_coeDeclAttr;
    v___x_4034_ = l_Lean_TagAttribute_hasTag(v___x_4033_, v_env_4031_, v_declName_4032_);
    return v___x_4034_;
}
pub unsafe fn l_Lean_Meta_isCoeDecl___boxed(
    mut v_env_4035_: *mut crate::leanh::LeanObject,
    mut v_declName_4036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4037_: u8 = 0;
    let mut v_r_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4037_ = l_Lean_Meta_isCoeDecl(v_env_4035_, v_declName_4036_);
    v_r_4038_ = crate::leanh::lean_box((v_res_4037_) as usize);
    return v_r_4038_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(
    mut v_declName_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = lean_st_ref_get(v___y_4040_);
    v_env_4043_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
    crate::leanh::lean_inc_ref(v_env_4043_);
    crate::leanh::lean_dec(v___x_4042_);
    v___x_4044_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4043_, v_declName_4039_);
    v___x_4045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4044_);
    return v___x_4045_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg___boxed(
    mut v_declName_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_4046_, v___y_4047_);
    crate::leanh::lean_dec(v___y_4047_);
    return v_res_4049_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(
    mut v_declName_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_declName_4050_, v___y_4054_);
    return v___x_4056_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___boxed(
    mut v_declName_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4063_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0(v_declName_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
    crate::leanh::lean_dec(v___y_4061_);
    crate::leanh::lean_dec_ref(v___y_4060_);
    crate::leanh::lean_dec(v___y_4059_);
    crate::leanh::lean_dec_ref(v___y_4058_);
    return v_res_4063_;
}
pub unsafe fn _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4064_ = crate::leanh::lean_box(0);
    v___x_4065_ = l_Lean_Expr_sort___override(v___x_4064_);
    return v___x_4065_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(
    mut v_e_4066_: *mut crate::leanh::LeanObject,
    mut v_nm_4067_: *mut crate::leanh::LeanObject,
    mut v_a_4068_: *mut crate::leanh::LeanObject,
    mut v_a_4069_: *mut crate::leanh::LeanObject,
    mut v_a_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v_val_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_a_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4100_: u8 = 0;
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_nm_4067_);
                v___x_4073_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget_spec__0___redArg(v_nm_4067_, v_a_4071_);
                if crate::leanh::lean_obj_tag(v___x_4073_) == 0 {
                    v_a_4074_ = crate::leanh::lean_ctor_get(v___x_4073_, 0);
                    v_isSharedCheck_4096_ = (!crate::leanh::lean_is_exclusive(v___x_4073_)) as u8;
                    if v_isSharedCheck_4096_ == 0 {
                        v___x_4076_ = v___x_4073_;
                        v_isShared_4077_ = v_isSharedCheck_4096_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4074_);
                        crate::leanh::lean_dec(v___x_4073_);
                        v___x_4076_ = crate::leanh::lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4096_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_nm_4067_);
                    crate::leanh::lean_dec_ref(v_e_4066_);
                    v_a_4097_ = crate::leanh::lean_ctor_get(v___x_4073_, 0);
                    v_isSharedCheck_4104_ = (!crate::leanh::lean_is_exclusive(v___x_4073_)) as u8;
                    if v_isSharedCheck_4104_ == 0 {
                        v___x_4099_ = v___x_4073_;
                        v_isShared_4100_ = v_isSharedCheck_4104_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4097_);
                        crate::leanh::lean_dec(v___x_4073_);
                        v___x_4099_ = crate::leanh::lean_box(0);
                        v_isShared_4100_ = v_isSharedCheck_4104_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4074_) == 1 {
                    v_val_4078_ = crate::leanh::lean_ctor_get(v_a_4074_, 0);
                    crate::leanh::lean_inc(v_val_4078_);
                    crate::leanh::lean_dec_ref_known(v_a_4074_, 1);
                    v_numParams_4079_ = crate::leanh::lean_ctor_get(v_val_4078_, 1);
                    crate::leanh::lean_inc(v_numParams_4079_);
                    crate::leanh::lean_dec(v_val_4078_);
                    v___x_4080_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once
                        ),
                        _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0,
                    );
                    v___x_4081_ = l_Lean_Expr_getAppNumArgs(v_e_4066_);
                    v___x_4082_ = lean_nat_sub(v___x_4081_, v_numParams_4079_);
                    crate::leanh::lean_dec(v_numParams_4079_);
                    crate::leanh::lean_dec(v___x_4081_);
                    v___x_4083_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4084_ = lean_nat_sub(v___x_4082_, v___x_4083_);
                    crate::leanh::lean_dec(v___x_4082_);
                    v___x_4085_ = l_Lean_Expr_getRevArgD(v_e_4066_, v___x_4084_, v___x_4080_);
                    crate::leanh::lean_dec_ref(v_e_4066_);
                    v___x_4086_ = l_Lean_Expr_getAppFn(v___x_4085_);
                    v___x_4087_ = l_Lean_Expr_isConst(v___x_4086_);
                    if v___x_4087_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4086_);
                        crate::leanh::lean_dec_ref(v___x_4085_);
                        if v_isShared_4077_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4076_, 0, v_nm_4067_);
                            v___x_4089_ = v___x_4076_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4090_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_nm_4067_);
                            v___x_4089_ = v_reuseFailAlloc_4090_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4076_);
                        crate::leanh::lean_dec(v_nm_4067_);
                        v___x_4091_ = l_Lean_Expr_constName_x21(v___x_4086_);
                        crate::leanh::lean_dec_ref(v___x_4086_);
                        v_e_4066_ = v___x_4085_;
                        v_nm_4067_ = v___x_4091_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4074_);
                    crate::leanh::lean_dec_ref(v_e_4066_);
                    if v_isShared_4077_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4076_, 0, v_nm_4067_);
                        v___x_4094_ = v___x_4076_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_nm_4067_);
                        v___x_4094_ = v_reuseFailAlloc_4095_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4089_;
            }
            3 => {
                return v___x_4094_;
            }
            4 => {
                if v_isShared_4100_ == 0 {
                    v___x_4102_ = v___x_4099_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4103_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
                    v___x_4102_ = v_reuseFailAlloc_4103_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___boxed(
    mut v_e_4105_: *mut crate::leanh::LeanObject,
    mut v_nm_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
    mut v_a_4108_: *mut crate::leanh::LeanObject,
    mut v_a_4109_: *mut crate::leanh::LeanObject,
    mut v_a_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4112_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(
        v_e_4105_, v_nm_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_,
    );
    crate::leanh::lean_dec(v_a_4110_);
    crate::leanh::lean_dec_ref(v_a_4109_);
    crate::leanh::lean_dec(v_a_4108_);
    crate::leanh::lean_dec_ref(v_a_4107_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_Meta_expandCoe___lam__0(
    mut v_e_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4120_, 0, v_e_4113_);
    v___x_4121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4121_, 0, v___x_4120_);
    crate::leanh::lean_ctor_set(v___x_4121_, 1, v___y_4114_);
    v___x_4122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4122_, 0, v___x_4121_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_Meta_expandCoe___lam__0___boxed(
    mut v_e_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_Meta_expandCoe___lam__0(
        v_e_4123_,
        v___y_4124_,
        v___y_4125_,
        v___y_4126_,
        v___y_4127_,
        v___y_4128_,
    );
    crate::leanh::lean_dec(v___y_4128_);
    crate::leanh::lean_dec_ref(v___y_4127_);
    crate::leanh::lean_dec(v___y_4126_);
    crate::leanh::lean_dec_ref(v___y_4125_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(
    mut v_msgData_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = lean_st_ref_get(v___y_4135_);
    v_env_4138_ = crate::leanh::lean_ctor_get(v___x_4137_, 0);
    crate::leanh::lean_inc_ref(v_env_4138_);
    crate::leanh::lean_dec(v___x_4137_);
    v___x_4139_ = lean_st_ref_get(v___y_4133_);
    v_mctx_4140_ = crate::leanh::lean_ctor_get(v___x_4139_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4140_);
    crate::leanh::lean_dec(v___x_4139_);
    v_lctx_4141_ = crate::leanh::lean_ctor_get(v___y_4132_, 2);
    v_options_4142_ = crate::leanh::lean_ctor_get(v___y_4134_, 2);
    crate::leanh::lean_inc_ref(v_options_4142_);
    crate::leanh::lean_inc_ref(v_lctx_4141_);
    v___x_4143_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4143_, 0, v_env_4138_);
    crate::leanh::lean_ctor_set(v___x_4143_, 1, v_mctx_4140_);
    crate::leanh::lean_ctor_set(v___x_4143_, 2, v_lctx_4141_);
    crate::leanh::lean_ctor_set(v___x_4143_, 3, v_options_4142_);
    v___x_4144_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4144_, 0, v___x_4143_);
    crate::leanh::lean_ctor_set(v___x_4144_, 1, v_msgData_4131_);
    v___x_4145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4145_, 0, v___x_4144_);
    return v___x_4145_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_msgData_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msgData_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
    crate::leanh::lean_dec(v___y_4150_);
    crate::leanh::lean_dec_ref(v___y_4149_);
    crate::leanh::lean_dec(v___y_4148_);
    crate::leanh::lean_dec_ref(v___y_4147_);
    return v_res_4152_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0()
-> f64 {
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: f64 = 0.0;
    v___x_4153_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4154_ = lean_float_of_nat(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(
    mut v_cls_4158_: *mut crate::leanh::LeanObject,
    mut v_msg_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4171_: u8 = 0;
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v_tid_4185_: u64 = 0;
    let mut v_traces_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: f64 = 0.0;
    let mut v___x_4192_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4166_ = crate::leanh::lean_ctor_get(v___y_4163_, 5);
                v___x_4167_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_4159_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
                v_a_4168_ = crate::leanh::lean_ctor_get(v___x_4167_, 0);
                v_isSharedCheck_4213_ = (!crate::leanh::lean_is_exclusive(v___x_4167_)) as u8;
                if v_isSharedCheck_4213_ == 0 {
                    v___x_4170_ = v___x_4167_;
                    v_isShared_4171_ = v_isSharedCheck_4213_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4168_);
                    crate::leanh::lean_dec(v___x_4167_);
                    v___x_4170_ = crate::leanh::lean_box(0);
                    v_isShared_4171_ = v_isSharedCheck_4213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4172_ = lean_st_ref_take(v___y_4164_);
                v_traceState_4173_ = crate::leanh::lean_ctor_get(v___x_4172_, 4);
                v_env_4174_ = crate::leanh::lean_ctor_get(v___x_4172_, 0);
                v_nextMacroScope_4175_ = crate::leanh::lean_ctor_get(v___x_4172_, 1);
                v_ngen_4176_ = crate::leanh::lean_ctor_get(v___x_4172_, 2);
                v_auxDeclNGen_4177_ = crate::leanh::lean_ctor_get(v___x_4172_, 3);
                v_cache_4178_ = crate::leanh::lean_ctor_get(v___x_4172_, 5);
                v_messages_4179_ = crate::leanh::lean_ctor_get(v___x_4172_, 6);
                v_infoState_4180_ = crate::leanh::lean_ctor_get(v___x_4172_, 7);
                v_snapshotTasks_4181_ = crate::leanh::lean_ctor_get(v___x_4172_, 8);
                v_isSharedCheck_4212_ = (!crate::leanh::lean_is_exclusive(v___x_4172_)) as u8;
                if v_isSharedCheck_4212_ == 0 {
                    v___x_4183_ = v___x_4172_;
                    v_isShared_4184_ = v_isSharedCheck_4212_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4181_);
                    crate::leanh::lean_inc(v_infoState_4180_);
                    crate::leanh::lean_inc(v_messages_4179_);
                    crate::leanh::lean_inc(v_cache_4178_);
                    crate::leanh::lean_inc(v_traceState_4173_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4177_);
                    crate::leanh::lean_inc(v_ngen_4176_);
                    crate::leanh::lean_inc(v_nextMacroScope_4175_);
                    crate::leanh::lean_inc(v_env_4174_);
                    crate::leanh::lean_dec(v___x_4172_);
                    v___x_4183_ = crate::leanh::lean_box(0);
                    v_isShared_4184_ = v_isSharedCheck_4212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4185_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4173_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4186_ = crate::leanh::lean_ctor_get(v_traceState_4173_, 0);
                v_isSharedCheck_4211_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4173_)) as u8;
                if v_isSharedCheck_4211_ == 0 {
                    v___x_4188_ = v_traceState_4173_;
                    v_isShared_4189_ = v_isSharedCheck_4211_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4186_);
                    crate::leanh::lean_dec(v_traceState_4173_);
                    v___x_4188_ = crate::leanh::lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4211_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4190_ = crate::leanh::lean_box(0);
                v___x_4191_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__0);
                v___x_4192_ = 0;
                v___x_4193_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1;
                v___x_4194_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4194_, 0, v_cls_4158_);
                crate::leanh::lean_ctor_set(v___x_4194_, 1, v___x_4190_);
                crate::leanh::lean_ctor_set(v___x_4194_, 2, v___x_4193_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4194_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4191_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4194_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4191_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4194_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4192_,
                );
                v___x_4195_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__2;
                v___x_4196_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4196_, 0, v___x_4194_);
                crate::leanh::lean_ctor_set(v___x_4196_, 1, v_a_4168_);
                crate::leanh::lean_ctor_set(v___x_4196_, 2, v___x_4195_);
                crate::leanh::lean_inc(v_ref_4166_);
                v___x_4197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4197_, 0, v_ref_4166_);
                crate::leanh::lean_ctor_set(v___x_4197_, 1, v___x_4196_);
                v___x_4198_ = l_Lean_PersistentArray_push___redArg(v_traces_4186_, v___x_4197_);
                if v_isShared_4189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4188_, 0, v___x_4198_);
                    v___x_4200_ = v___x_4188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4198_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4210_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4185_,
                    );
                    v___x_4200_ = v_reuseFailAlloc_4210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4183_, 4, v___x_4200_);
                    v___x_4202_ = v___x_4183_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_env_4174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_nextMacroScope_4175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_ngen_4176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_auxDeclNGen_4177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 4, v___x_4200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 5, v_cache_4178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 6, v_messages_4179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 7, v_infoState_4180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 8, v_snapshotTasks_4181_);
                    v___x_4202_ = v_reuseFailAlloc_4209_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4203_ = lean_st_ref_set(v___y_4164_, v___x_4202_);
                v___x_4204_ = crate::leanh::lean_box(0);
                v___x_4205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
                crate::leanh::lean_ctor_set(v___x_4205_, 1, v___y_4160_);
                if v_isShared_4171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4170_, 0, v___x_4205_);
                    v___x_4207_ = v___x_4170_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
                    v___x_4207_ = v_reuseFailAlloc_4208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___boxed(
    mut v_cls_4214_: *mut crate::leanh::LeanObject,
    mut v_msg_4215_: *mut crate::leanh::LeanObject,
    mut v___y_4216_: *mut crate::leanh::LeanObject,
    mut v___y_4217_: *mut crate::leanh::LeanObject,
    mut v___y_4218_: *mut crate::leanh::LeanObject,
    mut v___y_4219_: *mut crate::leanh::LeanObject,
    mut v___y_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4222_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_4214_, v_msg_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
    crate::leanh::lean_dec(v___y_4220_);
    crate::leanh::lean_dec_ref(v___y_4219_);
    crate::leanh::lean_dec(v___y_4218_);
    crate::leanh::lean_dec_ref(v___y_4217_);
    return v_res_4222_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_keys_4223_: *mut crate::leanh::LeanObject,
    mut v_i_4224_: *mut crate::leanh::LeanObject,
    mut v_k_4225_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v_k_x27_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4226_ = lean_array_get_size(v_keys_4223_);
                v___x_4227_ = lean_nat_dec_lt(v_i_4224_, v___x_4226_);
                if v___x_4227_ == 0 {
                    crate::leanh::lean_dec(v_i_4224_);
                    return v___x_4227_;
                } else {
                    v_k_x27_4228_ = lean_array_fget_borrowed(v_keys_4223_, v_i_4224_);
                    v___x_4229_ = l_Lean_instBEqExtraModUse_beq(v_k_4225_, v_k_x27_4228_);
                    if v___x_4229_ == 0 {
                        v___x_4230_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4231_ = lean_nat_add(v_i_4224_, v___x_4230_);
                        crate::leanh::lean_dec(v_i_4224_);
                        v_i_4224_ = v___x_4231_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4224_);
                        return v___x_4229_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_keys_4233_: *mut crate::leanh::LeanObject,
    mut v_i_4234_: *mut crate::leanh::LeanObject,
    mut v_k_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4236_: u8 = 0;
    let mut v_r_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4236_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_4233_, v_i_4234_, v_k_4235_);
    crate::leanh::lean_dec_ref(v_k_4235_);
    crate::leanh::lean_dec_ref(v_keys_4233_);
    v_r_4237_ = crate::leanh::lean_box((v_res_4236_) as usize);
    return v_r_4237_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_4238_: usize = 0;
    let mut v___x_4239_: usize = 0;
    let mut v___x_4240_: usize = 0;
    v___x_4238_ = 5usize;
    v___x_4239_ = 1usize;
    v___x_4240_ = lean_usize_shift_left(v___x_4239_, v___x_4238_);
    return v___x_4240_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_4241_: usize = 0;
    let mut v___x_4242_: usize = 0;
    let mut v___x_4243_: usize = 0;
    v___x_4241_ = 1usize;
    v___x_4242_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
    v___x_4243_ = lean_usize_sub(v___x_4242_, v___x_4241_);
    return v___x_4243_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_4244_: *mut crate::leanh::LeanObject,
    mut v_x_4245_: usize,
    mut v_x_4246_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: usize = 0;
    let mut v___x_4250_: usize = 0;
    let mut v___x_4251_: usize = 0;
    let mut v_j_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v_node_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: usize = 0;
    let mut v___x_4259_: u8 = 0;
    let mut v_ks_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4244_) == 0 {
                    v_es_4247_ = crate::leanh::lean_ctor_get(v_x_4244_, 0);
                    v___x_4248_ = crate::leanh::lean_box(2);
                    v___x_4249_ = 5usize;
                    v___x_4250_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4251_ = lean_usize_land(v_x_4245_, v___x_4250_);
                    v_j_4252_ = lean_usize_to_nat(v___x_4251_);
                    v___x_4253_ = lean_array_get_borrowed(v___x_4248_, v_es_4247_, v_j_4252_);
                    crate::leanh::lean_dec(v_j_4252_);
                    match crate::leanh::lean_obj_tag(v___x_4253_) {
                        0 => {
                            v_key_4254_ = crate::leanh::lean_ctor_get(v___x_4253_, 0);
                            v___x_4255_ = l_Lean_instBEqExtraModUse_beq(v_x_4246_, v_key_4254_);
                            return v___x_4255_;
                        }
                        1 => {
                            v_node_4256_ = crate::leanh::lean_ctor_get(v___x_4253_, 0);
                            v___x_4257_ = lean_usize_shift_right(v_x_4245_, v___x_4249_);
                            v_x_4244_ = v_node_4256_;
                            v_x_4245_ = v___x_4257_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4259_ = 0;
                            return v___x_4259_;
                        }
                    }
                } else {
                    v_ks_4260_ = crate::leanh::lean_ctor_get(v_x_4244_, 0);
                    v___x_4261_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4262_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_4260_, v___x_4261_, v_x_4246_);
                    return v___x_4262_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_4263_: *mut crate::leanh::LeanObject,
    mut v_x_4264_: *mut crate::leanh::LeanObject,
    mut v_x_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37481__boxed_4266_: usize = 0;
    let mut v_res_4267_: u8 = 0;
    let mut v_r_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37481__boxed_4266_ = crate::leanh::lean_unbox_usize(v_x_4264_);
    crate::leanh::lean_dec(v_x_4264_);
    v_res_4267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4263_, v_x_37481__boxed_4266_, v_x_4265_);
    crate::leanh::lean_dec_ref(v_x_4265_);
    crate::leanh::lean_dec_ref(v_x_4263_);
    v_r_4268_ = crate::leanh::lean_box((v_res_4267_) as usize);
    return v_r_4268_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(
    mut v_x_4269_: *mut crate::leanh::LeanObject,
    mut v_x_4270_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4271_: u64 = 0;
    let mut v___x_4272_: usize = 0;
    let mut v___x_4273_: u8 = 0;
    v___x_4271_ = l_Lean_instHashableExtraModUse_hash(v_x_4270_);
    v___x_4272_ = lean_uint64_to_usize(v___x_4271_);
    v___x_4273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4269_, v___x_4272_, v_x_4270_);
    return v___x_4273_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4274_: *mut crate::leanh::LeanObject,
    mut v_x_4275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4276_: u8 = 0;
    let mut v_r_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4276_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_4274_, v_x_4275_);
    crate::leanh::lean_dec_ref(v_x_4275_);
    crate::leanh::lean_dec_ref(v_x_4274_);
    v_r_4277_ = crate::leanh::lean_box((v_res_4276_) as usize);
    return v_r_4277_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4280_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__1;
    v___x_4281_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__0;
    v___x_4282_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4281_,
        v___x_4280_,
    );
    return v___x_4282_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4283_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4283_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__3);
    v___x_4285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4285_, 0, v___x_4284_);
    return v___x_4285_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
    v___x_4287_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4287_, 0, v___x_4286_);
    crate::leanh::lean_ctor_set(v___x_4287_, 1, v___x_4286_);
    return v___x_4287_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4288_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__4);
    v___x_4289_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4289_, 0, v___x_4288_);
    crate::leanh::lean_ctor_set(v___x_4289_, 1, v___x_4288_);
    crate::leanh::lean_ctor_set(v___x_4289_, 2, v___x_4288_);
    crate::leanh::lean_ctor_set(v___x_4289_, 3, v___x_4288_);
    crate::leanh::lean_ctor_set(v___x_4289_, 4, v___x_4288_);
    crate::leanh::lean_ctor_set(v___x_4289_, 5, v___x_4288_);
    return v___x_4289_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__9;
    v___x_4295_ = l_Lean_stringToMessageData(v___x_4294_);
    return v___x_4295_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__11;
    v___x_4298_ = l_Lean_stringToMessageData(v___x_4297_);
    return v___x_4298_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4299_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2___closed__1;
    v___x_4300_ = l_Lean_stringToMessageData(v___x_4299_);
    return v___x_4300_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_4304_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8;
    v___x_4305_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__15;
    v___x_4306_ = l_Lean_Name_append(v___x_4305_, v_cls_4304_);
    return v___x_4306_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__17;
    v___x_4309_ = l_Lean_stringToMessageData(v___x_4308_);
    return v___x_4309_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4311_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__19;
    v___x_4312_ = l_Lean_stringToMessageData(v___x_4311_);
    return v___x_4312_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(
    mut v_mod_4317_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4318_: u8,
    mut v_hint_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4328_: u8 = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v_asyncMode_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_unused_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4378_: u8 = 0;
    let mut v_unused_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: u8 = 0;
    let mut v_options_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4383_: u8 = 0;
    let mut v_inheritedTraceOptions_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4326_ = lean_st_ref_get(v___y_4324_);
                v_env_4327_ = crate::leanh::lean_ctor_get(v___x_4326_, 0);
                crate::leanh::lean_inc_ref(v_env_4327_);
                crate::leanh::lean_dec(v___x_4326_);
                v_isExporting_4328_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4327_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4327_);
                v___x_4329_ = lean_st_ref_get(v___y_4324_);
                v_env_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                crate::leanh::lean_inc_ref(v_env_4330_);
                crate::leanh::lean_dec(v___x_4329_);
                v___x_4331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__2);
                crate::leanh::lean_inc(v_mod_4317_);
                v_entry_4332_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_4332_, 0, v_mod_4317_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4332_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_4328_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4332_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4318_,
                );
                v___x_4333_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4334_ = crate::leanh::lean_box(1);
                v___x_4335_ = crate::leanh::lean_box(0);
                v___x_4380_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4331_,
                    v___x_4333_,
                    v_env_4330_,
                    v___x_4334_,
                    v___x_4335_,
                );
                v___x_4381_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v___x_4380_, v_entry_4332_);
                crate::leanh::lean_dec(v___x_4380_);
                if v___x_4381_ == 0 {
                    v_options_4382_ = crate::leanh::lean_ctor_get(v___y_4323_, 2);
                    v_hasTrace_4383_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4382_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4383_ == 0 {
                        crate::leanh::lean_dec(v_hint_4319_);
                        crate::leanh::lean_dec(v_mod_4317_);
                        v___y_4337_ = v___y_4320_;
                        v___y_4338_ = v___y_4322_;
                        v___y_4339_ = v___y_4324_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4384_ =
                            crate::leanh::lean_ctor_get(v___y_4323_, 13);
                        v_cls_4385_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__8;
                        v___x_4407_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__16);
                        v___x_4408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4384_,
                            v_options_4382_,
                            v___x_4407_,
                        );
                        if v___x_4408_ == 0 {
                            crate::leanh::lean_dec(v_hint_4319_);
                            crate::leanh::lean_dec(v_mod_4317_);
                            v___y_4337_ = v___y_4320_;
                            v___y_4338_ = v___y_4322_;
                            v___y_4339_ = v___y_4324_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__18);
                            if v_isExporting_4328_ == 0 {
                                v___x_4418_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__23;
                                v___y_4411_ = v___x_4418_;
                                state = 8;
                                continue;
                            } else {
                                v___x_4419_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__24;
                                v___y_4411_ = v___x_4419_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4332_, 1);
                    crate::leanh::lean_dec(v_hint_4319_);
                    crate::leanh::lean_dec(v_mod_4317_);
                    v___x_4420_ = crate::leanh::lean_box(0);
                    v___x_4421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4420_);
                    crate::leanh::lean_ctor_set(v___x_4421_, 1, v___y_4320_);
                    v___x_4422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4422_, 0, v___x_4421_);
                    return v___x_4422_;
                }
            }
            1 => {
                v___x_4340_ = lean_st_ref_take(v___y_4339_);
                v_toEnvExtension_4341_ = crate::leanh::lean_ctor_get(v___x_4333_, 0);
                v_env_4342_ = crate::leanh::lean_ctor_get(v___x_4340_, 0);
                v_nextMacroScope_4343_ = crate::leanh::lean_ctor_get(v___x_4340_, 1);
                v_ngen_4344_ = crate::leanh::lean_ctor_get(v___x_4340_, 2);
                v_auxDeclNGen_4345_ = crate::leanh::lean_ctor_get(v___x_4340_, 3);
                v_traceState_4346_ = crate::leanh::lean_ctor_get(v___x_4340_, 4);
                v_messages_4347_ = crate::leanh::lean_ctor_get(v___x_4340_, 6);
                v_infoState_4348_ = crate::leanh::lean_ctor_get(v___x_4340_, 7);
                v_snapshotTasks_4349_ = crate::leanh::lean_ctor_get(v___x_4340_, 8);
                v_isSharedCheck_4378_ = (!crate::leanh::lean_is_exclusive(v___x_4340_)) as u8;
                if v_isSharedCheck_4378_ == 0 {
                    v_unused_4379_ = crate::leanh::lean_ctor_get(v___x_4340_, 5);
                    crate::leanh::lean_dec(v_unused_4379_);
                    v___x_4351_ = v___x_4340_;
                    v_isShared_4352_ = v_isSharedCheck_4378_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4349_);
                    crate::leanh::lean_inc(v_infoState_4348_);
                    crate::leanh::lean_inc(v_messages_4347_);
                    crate::leanh::lean_inc(v_traceState_4346_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4345_);
                    crate::leanh::lean_inc(v_ngen_4344_);
                    crate::leanh::lean_inc(v_nextMacroScope_4343_);
                    crate::leanh::lean_inc(v_env_4342_);
                    crate::leanh::lean_dec(v___x_4340_);
                    v___x_4351_ = crate::leanh::lean_box(0);
                    v_isShared_4352_ = v_isSharedCheck_4378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4353_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4341_, 2);
                v___x_4354_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4333_,
                    v_env_4342_,
                    v_entry_4332_,
                    v_asyncMode_4353_,
                    v___x_4335_,
                );
                v___x_4355_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__5);
                if v_isShared_4352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4351_, 5, v___x_4355_);
                    crate::leanh::lean_ctor_set(v___x_4351_, 0, v___x_4354_);
                    v___x_4357_ = v___x_4351_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4377_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 1, v_nextMacroScope_4343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 2, v_ngen_4344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 3, v_auxDeclNGen_4345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 4, v_traceState_4346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 5, v___x_4355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 6, v_messages_4347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 7, v_infoState_4348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 8, v_snapshotTasks_4349_);
                    v___x_4357_ = v_reuseFailAlloc_4377_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4358_ = lean_st_ref_set(v___y_4339_, v___x_4357_);
                v___x_4359_ = lean_st_ref_take(v___y_4338_);
                v_mctx_4360_ = crate::leanh::lean_ctor_get(v___x_4359_, 0);
                v_zetaDeltaFVarIds_4361_ = crate::leanh::lean_ctor_get(v___x_4359_, 2);
                v_postponed_4362_ = crate::leanh::lean_ctor_get(v___x_4359_, 3);
                v_diag_4363_ = crate::leanh::lean_ctor_get(v___x_4359_, 4);
                v_isSharedCheck_4375_ = (!crate::leanh::lean_is_exclusive(v___x_4359_)) as u8;
                if v_isSharedCheck_4375_ == 0 {
                    v_unused_4376_ = crate::leanh::lean_ctor_get(v___x_4359_, 1);
                    crate::leanh::lean_dec(v_unused_4376_);
                    v___x_4365_ = v___x_4359_;
                    v_isShared_4366_ = v_isSharedCheck_4375_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4363_);
                    crate::leanh::lean_inc(v_postponed_4362_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4361_);
                    crate::leanh::lean_inc(v_mctx_4360_);
                    crate::leanh::lean_dec(v___x_4359_);
                    v___x_4365_ = crate::leanh::lean_box(0);
                    v_isShared_4366_ = v_isSharedCheck_4375_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4367_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__6);
                if v_isShared_4366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4365_, 1, v___x_4367_);
                    v___x_4369_ = v___x_4365_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_mctx_4360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 1, v___x_4367_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4374_,
                        2,
                        v_zetaDeltaFVarIds_4361_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 3, v_postponed_4362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 4, v_diag_4363_);
                    v___x_4369_ = v_reuseFailAlloc_4374_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4370_ = lean_st_ref_set(v___y_4338_, v___x_4369_);
                v___x_4371_ = crate::leanh::lean_box(0);
                v___x_4372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4372_, 0, v___x_4371_);
                crate::leanh::lean_ctor_set(v___x_4372_, 1, v___y_4337_);
                v___x_4373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4372_);
                return v___x_4373_;
            }
            6 => {
                v___x_4389_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4389_, 0, v___y_4387_);
                crate::leanh::lean_ctor_set(v___x_4389_, 1, v___y_4388_);
                v___x_4390_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2(v_cls_4385_, v___x_4389_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
                if crate::leanh::lean_obj_tag(v___x_4390_) == 0 {
                    v_a_4391_ = crate::leanh::lean_ctor_get(v___x_4390_, 0);
                    crate::leanh::lean_inc(v_a_4391_);
                    crate::leanh::lean_dec_ref_known(v___x_4390_, 1);
                    v_snd_4392_ = crate::leanh::lean_ctor_get(v_a_4391_, 1);
                    crate::leanh::lean_inc(v_snd_4392_);
                    crate::leanh::lean_dec(v_a_4391_);
                    v___y_4337_ = v_snd_4392_;
                    v___y_4338_ = v___y_4322_;
                    v___y_4339_ = v___y_4324_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4332_, 1);
                    return v___x_4390_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_4395_);
                v___x_4396_ = l_Lean_stringToMessageData(v___y_4395_);
                v___x_4397_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4397_, 0, v___y_4394_);
                crate::leanh::lean_ctor_set(v___x_4397_, 1, v___x_4396_);
                v___x_4398_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__10);
                v___x_4399_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4399_, 0, v___x_4397_);
                crate::leanh::lean_ctor_set(v___x_4399_, 1, v___x_4398_);
                v___x_4400_ = l_Lean_MessageData_ofName(v_mod_4317_);
                v___x_4401_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4401_, 0, v___x_4399_);
                crate::leanh::lean_ctor_set(v___x_4401_, 1, v___x_4400_);
                v___x_4402_ = l_Lean_Name_isAnonymous(v_hint_4319_);
                if v___x_4402_ == 0 {
                    v___x_4403_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__12);
                    v___x_4404_ = l_Lean_MessageData_ofName(v_hint_4319_);
                    v___x_4405_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4405_, 0, v___x_4403_);
                    crate::leanh::lean_ctor_set(v___x_4405_, 1, v___x_4404_);
                    v___y_4387_ = v___x_4401_;
                    v___y_4388_ = v___x_4405_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_4319_);
                    v___x_4406_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__13);
                    v___y_4387_ = v___x_4401_;
                    v___y_4388_ = v___x_4406_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_4411_);
                v___x_4412_ = l_Lean_stringToMessageData(v___y_4411_);
                v___x_4413_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4413_, 0, v___x_4409_);
                crate::leanh::lean_ctor_set(v___x_4413_, 1, v___x_4412_);
                v___x_4414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__20);
                v___x_4415_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4415_, 0, v___x_4413_);
                crate::leanh::lean_ctor_set(v___x_4415_, 1, v___x_4414_);
                if v_isMeta_4318_ == 0 {
                    v___x_4416_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__21;
                    v___y_4394_ = v___x_4415_;
                    v___y_4395_ = v___x_4416_;
                    state = 7;
                    continue;
                } else {
                    v___x_4417_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___closed__22;
                    v___y_4394_ = v___x_4415_;
                    v___y_4395_ = v___x_4417_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0___boxed(
    mut v_mod_4423_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4424_: *mut crate::leanh::LeanObject,
    mut v_hint_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4432_: u8 = 0;
    let mut v_res_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4432_ = (crate::leanh::lean_unbox(v_isMeta_4424_) as u8);
    v_res_4433_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_mod_4423_, v_isMeta_boxed_4432_, v_hint_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
    crate::leanh::lean_dec(v___y_4430_);
    crate::leanh::lean_dec_ref(v___y_4429_);
    crate::leanh::lean_dec(v___y_4428_);
    crate::leanh::lean_dec_ref(v___y_4427_);
    return v_res_4433_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_x_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4435_) == 0 {
                    v___x_4436_ = crate::leanh::lean_box(0);
                    return v___x_4436_;
                } else {
                    v_key_4437_ = crate::leanh::lean_ctor_get(v_x_4435_, 0);
                    v_value_4438_ = crate::leanh::lean_ctor_get(v_x_4435_, 1);
                    v_tail_4439_ = crate::leanh::lean_ctor_get(v_x_4435_, 2);
                    v___x_4440_ = lean_name_eq(v_key_4437_, v_a_4434_);
                    if v___x_4440_ == 0 {
                        v_x_4435_ = v_tail_4439_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4438_);
                        v___x_4442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4442_, 0, v_value_4438_);
                        return v___x_4442_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_a_4443_: *mut crate::leanh::LeanObject,
    mut v_x_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_4443_, v_x_4444_);
    crate::leanh::lean_dec(v_x_4444_);
    crate::leanh::lean_dec(v_a_4443_);
    return v_res_4445_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u64 = 0;
    v___x_4446_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4447_ = lean_uint64_of_nat(v___x_4446_);
    return v___x_4447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(
    mut v_m_4448_: *mut crate::leanh::LeanObject,
    mut v_a_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4453_: u64 = 0;
    let mut v___x_4454_: u64 = 0;
    let mut v___x_4455_: u64 = 0;
    let mut v_fold_4456_: u64 = 0;
    let mut v___x_4457_: u64 = 0;
    let mut v___x_4458_: u64 = 0;
    let mut v___x_4459_: u64 = 0;
    let mut v___x_4460_: usize = 0;
    let mut v___x_4461_: usize = 0;
    let mut v___x_4462_: usize = 0;
    let mut v___x_4463_: usize = 0;
    let mut v___x_4464_: usize = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u64 = 0;
    let mut v_hash_4468_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4450_ = crate::leanh::lean_ctor_get(v_m_4448_, 1);
                v___x_4451_ = lean_array_get_size(v_buckets_4450_);
                if crate::leanh::lean_obj_tag(v_a_4449_) == 0 {
                    v___x_4467_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___closed__0);
                    v___y_4453_ = v___x_4467_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4468_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4449_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4453_ = v_hash_4468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4454_ = 32u64;
                v___x_4455_ = lean_uint64_shift_right(v___y_4453_, v___x_4454_);
                v_fold_4456_ = lean_uint64_xor(v___y_4453_, v___x_4455_);
                v___x_4457_ = 16u64;
                v___x_4458_ = lean_uint64_shift_right(v_fold_4456_, v___x_4457_);
                v___x_4459_ = lean_uint64_xor(v_fold_4456_, v___x_4458_);
                v___x_4460_ = lean_uint64_to_usize(v___x_4459_);
                v___x_4461_ = lean_usize_of_nat(v___x_4451_);
                v___x_4462_ = 1usize;
                v___x_4463_ = lean_usize_sub(v___x_4461_, v___x_4462_);
                v___x_4464_ = lean_usize_land(v___x_4460_, v___x_4463_);
                v___x_4465_ = lean_array_uget_borrowed(v_buckets_4450_, v___x_4464_);
                v___x_4466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_4449_, v___x_4465_);
                return v___x_4466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg___boxed(
    mut v_m_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_4469_, v_a_4470_);
    crate::leanh::lean_dec(v_a_4470_);
    crate::leanh::lean_dec_ref(v_m_4469_);
    return v_res_4471_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(
    mut v___x_4472_: *mut crate::leanh::LeanObject,
    mut v_declName_4473_: *mut crate::leanh::LeanObject,
    mut v_as_4474_: *mut crate::leanh::LeanObject,
    mut v_sz_4475_: usize,
    mut v_i_4476_: usize,
    mut v_b_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4484_: u8 = 0;
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: usize = 0;
    let mut v___x_4500_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4484_ = lean_usize_dec_lt(v_i_4476_, v_sz_4475_);
                if v___x_4484_ == 0 {
                    crate::leanh::lean_dec(v_declName_4473_);
                    v___x_4485_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4485_, 0, v_b_4477_);
                    crate::leanh::lean_ctor_set(v___x_4485_, 1, v___y_4478_);
                    v___x_4486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4486_, 0, v___x_4485_);
                    return v___x_4486_;
                } else {
                    v___x_4487_ = l_Lean_Environment_header(v___x_4472_);
                    v_modules_4488_ = crate::leanh::lean_ctor_get(v___x_4487_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4488_);
                    crate::leanh::lean_dec_ref(v___x_4487_);
                    v___x_4489_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4490_ = lean_array_uget_borrowed(v_as_4474_, v_i_4476_);
                    v___x_4491_ = lean_array_get(v___x_4489_, v_modules_4488_, v_a_4490_);
                    crate::leanh::lean_dec_ref(v_modules_4488_);
                    v_toImport_4492_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_4492_);
                    crate::leanh::lean_dec(v___x_4491_);
                    v_module_4493_ = crate::leanh::lean_ctor_get(v_toImport_4492_, 0);
                    crate::leanh::lean_inc(v_module_4493_);
                    crate::leanh::lean_dec_ref(v_toImport_4492_);
                    v___x_4494_ = 0;
                    crate::leanh::lean_inc(v_declName_4473_);
                    v___x_4495_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_4493_, v___x_4494_, v_declName_4473_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
                    if crate::leanh::lean_obj_tag(v___x_4495_) == 0 {
                        v_a_4496_ = crate::leanh::lean_ctor_get(v___x_4495_, 0);
                        crate::leanh::lean_inc(v_a_4496_);
                        crate::leanh::lean_dec_ref_known(v___x_4495_, 1);
                        v_snd_4497_ = crate::leanh::lean_ctor_get(v_a_4496_, 1);
                        crate::leanh::lean_inc(v_snd_4497_);
                        crate::leanh::lean_dec(v_a_4496_);
                        v___x_4498_ = crate::leanh::lean_box(0);
                        v___x_4499_ = 1usize;
                        v___x_4500_ = lean_usize_add(v_i_4476_, v___x_4499_);
                        v_i_4476_ = v___x_4500_;
                        v_b_4477_ = v___x_4498_;
                        v___y_4478_ = v_snd_4497_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_4473_);
                        return v___x_4495_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1___boxed(
    mut v___x_4502_: *mut crate::leanh::LeanObject,
    mut v_declName_4503_: *mut crate::leanh::LeanObject,
    mut v_as_4504_: *mut crate::leanh::LeanObject,
    mut v_sz_4505_: *mut crate::leanh::LeanObject,
    mut v_i_4506_: *mut crate::leanh::LeanObject,
    mut v_b_4507_: *mut crate::leanh::LeanObject,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4514_: usize = 0;
    let mut v_i_boxed_4515_: usize = 0;
    let mut v_res_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4514_ = crate::leanh::lean_unbox_usize(v_sz_4505_);
    crate::leanh::lean_dec(v_sz_4505_);
    v_i_boxed_4515_ = crate::leanh::lean_unbox_usize(v_i_4506_);
    crate::leanh::lean_dec(v_i_4506_);
    v_res_4516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v___x_4502_, v_declName_4503_, v_as_4504_, v_sz_boxed_4514_, v_i_boxed_4515_, v_b_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
    crate::leanh::lean_dec(v___y_4512_);
    crate::leanh::lean_dec_ref(v___y_4511_);
    crate::leanh::lean_dec(v___y_4510_);
    crate::leanh::lean_dec_ref(v___y_4509_);
    crate::leanh::lean_dec_ref(v_as_4504_);
    crate::leanh::lean_dec_ref(v___x_4502_);
    return v_res_4516_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__1;
    v___x_4520_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__0;
    v___x_4521_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4520_,
        v___x_4519_,
    );
    return v___x_4521_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(
    mut v_declName_4524_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4525_: u8,
    mut v___y_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4542_: usize = 0;
    let mut v___x_4543_: usize = 0;
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v_snd_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_unused_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4561_: u8 = 0;
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4573_: u8 = 0;
    let mut v_toImport_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: u8 = 0;
    let mut v___x_4587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4532_ = lean_st_ref_get(v___y_4530_);
                v_env_4537_ = crate::leanh::lean_ctor_get(v___x_4532_, 0);
                crate::leanh::lean_inc_ref(v_env_4537_);
                crate::leanh::lean_dec(v___x_4532_);
                v___x_4562_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4537_, v_declName_4524_);
                if crate::leanh::lean_obj_tag(v___x_4562_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_4537_);
                    crate::leanh::lean_dec(v_declName_4524_);
                    state = 1;
                    continue;
                } else {
                    v_val_4563_ = crate::leanh::lean_ctor_get(v___x_4562_, 0);
                    crate::leanh::lean_inc(v_val_4563_);
                    crate::leanh::lean_dec_ref_known(v___x_4562_, 1);
                    v___x_4564_ = l_Lean_Environment_header(v_env_4537_);
                    v_modules_4565_ = crate::leanh::lean_ctor_get(v___x_4564_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4565_);
                    crate::leanh::lean_dec_ref(v___x_4564_);
                    v___x_4566_ = lean_array_get_size(v_modules_4565_);
                    v___x_4567_ = lean_nat_dec_lt(v_val_4563_, v___x_4566_);
                    if v___x_4567_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_4565_);
                        crate::leanh::lean_dec(v_val_4563_);
                        crate::leanh::lean_dec_ref(v_env_4537_);
                        crate::leanh::lean_dec(v_declName_4524_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4568_ = lean_st_ref_get(v___y_4530_);
                        v_env_4569_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                        crate::leanh::lean_inc_ref(v_env_4569_);
                        crate::leanh::lean_dec(v___x_4568_);
                        v___x_4570_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__2);
                        v___x_4571_ = lean_array_fget(v_modules_4565_, v_val_4563_);
                        crate::leanh::lean_dec(v_val_4563_);
                        crate::leanh::lean_dec_ref(v_modules_4565_);
                        if v_isMeta_4525_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_4569_);
                            v___y_4573_ = v_isMeta_4525_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_4524_);
                            v___x_4586_ = l_Lean_isMarkedMeta(v_env_4569_, v_declName_4524_);
                            if v___x_4586_ == 0 {
                                v___y_4573_ = v_isMeta_4525_;
                                state = 7;
                                continue;
                            } else {
                                v___x_4587_ = 0;
                                v___y_4573_ = v___x_4587_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4534_ = crate::leanh::lean_box(0);
                v___x_4535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4535_, 0, v___x_4534_);
                crate::leanh::lean_ctor_set(v___x_4535_, 1, v___y_4526_);
                v___x_4536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4536_, 0, v___x_4535_);
                return v___x_4536_;
            }
            2 => {
                v___x_4541_ = crate::leanh::lean_box(0);
                v_sz_4542_ = lean_array_size(v___y_4540_);
                v___x_4543_ = 0usize;
                v___x_4544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__1(v_env_4537_, v_declName_4524_, v___y_4540_, v_sz_4542_, v___x_4543_, v___x_4541_, v___y_4539_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
                crate::leanh::lean_dec_ref(v___y_4540_);
                crate::leanh::lean_dec_ref(v_env_4537_);
                if crate::leanh::lean_obj_tag(v___x_4544_) == 0 {
                    v_a_4545_ = crate::leanh::lean_ctor_get(v___x_4544_, 0);
                    v_isSharedCheck_4561_ = (!crate::leanh::lean_is_exclusive(v___x_4544_)) as u8;
                    if v_isSharedCheck_4561_ == 0 {
                        v___x_4547_ = v___x_4544_;
                        v_isShared_4548_ = v_isSharedCheck_4561_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4545_);
                        crate::leanh::lean_dec(v___x_4544_);
                        v___x_4547_ = crate::leanh::lean_box(0);
                        v_isShared_4548_ = v_isSharedCheck_4561_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4544_;
                }
            }
            3 => {
                v_snd_4549_ = crate::leanh::lean_ctor_get(v_a_4545_, 1);
                v_isSharedCheck_4559_ = (!crate::leanh::lean_is_exclusive(v_a_4545_)) as u8;
                if v_isSharedCheck_4559_ == 0 {
                    v_unused_4560_ = crate::leanh::lean_ctor_get(v_a_4545_, 0);
                    crate::leanh::lean_dec(v_unused_4560_);
                    v___x_4551_ = v_a_4545_;
                    v_isShared_4552_ = v_isSharedCheck_4559_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4549_);
                    crate::leanh::lean_dec(v_a_4545_);
                    v___x_4551_ = crate::leanh::lean_box(0);
                    v_isShared_4552_ = v_isSharedCheck_4559_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4551_, 0, v___x_4541_);
                    v___x_4554_ = v___x_4551_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_snd_4549_);
                    v___x_4554_ = v_reuseFailAlloc_4558_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4547_, 0, v___x_4554_);
                    v___x_4556_ = v___x_4547_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
                    v___x_4556_ = v_reuseFailAlloc_4557_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4556_;
            }
            7 => {
                v_toImport_4574_ = crate::leanh::lean_ctor_get(v___x_4571_, 0);
                crate::leanh::lean_inc_ref(v_toImport_4574_);
                crate::leanh::lean_dec(v___x_4571_);
                v_module_4575_ = crate::leanh::lean_ctor_get(v_toImport_4574_, 0);
                crate::leanh::lean_inc(v_module_4575_);
                crate::leanh::lean_dec_ref(v_toImport_4574_);
                crate::leanh::lean_inc(v_declName_4524_);
                v___x_4576_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0(v_module_4575_, v___y_4573_, v_declName_4524_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
                if crate::leanh::lean_obj_tag(v___x_4576_) == 0 {
                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4576_, 0);
                    crate::leanh::lean_inc(v_a_4577_);
                    crate::leanh::lean_dec_ref_known(v___x_4576_, 1);
                    v_snd_4578_ = crate::leanh::lean_ctor_get(v_a_4577_, 1);
                    crate::leanh::lean_inc(v_snd_4578_);
                    crate::leanh::lean_dec(v_a_4577_);
                    v___x_4579_ = l_Lean_indirectModUseExt;
                    v___x_4580_ = crate::leanh::lean_box(1);
                    v___x_4581_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_4537_);
                    v___x_4582_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4570_,
                        v___x_4579_,
                        v_env_4537_,
                        v___x_4580_,
                        v___x_4581_,
                    );
                    v___x_4583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v___x_4582_, v_declName_4524_);
                    crate::leanh::lean_dec(v___x_4582_);
                    if crate::leanh::lean_obj_tag(v___x_4583_) == 0 {
                        v___x_4584_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___closed__3;
                        v___y_4539_ = v_snd_4578_;
                        v___y_4540_ = v___x_4584_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4585_ = crate::leanh::lean_ctor_get(v___x_4583_, 0);
                        crate::leanh::lean_inc(v_val_4585_);
                        crate::leanh::lean_dec_ref_known(v___x_4583_, 1);
                        v___y_4539_ = v_snd_4578_;
                        v___y_4540_ = v_val_4585_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4537_);
                    crate::leanh::lean_dec(v_declName_4524_);
                    return v___x_4576_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0___boxed(
    mut v_declName_4588_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
    mut v___y_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4596_: u8 = 0;
    let mut v_res_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4596_ = (crate::leanh::lean_unbox(v_isMeta_4589_) as u8);
    v_res_4597_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(
        v_declName_4588_,
        v_isMeta_boxed_4596_,
        v___y_4590_,
        v___y_4591_,
        v___y_4592_,
        v___y_4593_,
        v___y_4594_,
    );
    crate::leanh::lean_dec(v___y_4594_);
    crate::leanh::lean_dec_ref(v___y_4593_);
    crate::leanh::lean_dec(v___y_4592_);
    crate::leanh::lean_dec_ref(v___y_4591_);
    return v_res_4597_;
}
pub unsafe fn l_Lean_Meta_expandCoe___lam__1(
    mut v_e_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
    mut v___y_4610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v_val_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4640_: u8 = 0;
    let mut v___y_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: u8 = 0;
    let mut v_dummy_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: u8 = 0;
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4669_: u8 = 0;
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_a_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4674_: u8 = 0;
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut v_unused_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4688_: u8 = 0;
    let mut v_a_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4692_: u8 = 0;
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_4617_ = l_Lean_Expr_getAppFn(v_e_4605_);
                v___x_4618_ = l_Lean_Expr_isConst(v_f_4617_);
                if v___x_4618_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_4617_);
                    crate::leanh::lean_dec_ref(v_e_4605_);
                    v___y_4613_ = v___y_4606_;
                    state = 1;
                    continue;
                } else {
                    v___x_4619_ = lean_st_ref_get(v___y_4610_);
                    v_env_4620_ = crate::leanh::lean_ctor_get(v___x_4619_, 0);
                    crate::leanh::lean_inc_ref(v_env_4620_);
                    crate::leanh::lean_dec(v___x_4619_);
                    v_declName_4621_ = l_Lean_Expr_constName_x21(v_f_4617_);
                    crate::leanh::lean_dec_ref(v_f_4617_);
                    crate::leanh::lean_inc(v_declName_4621_);
                    v___x_4622_ = l_Lean_Meta_isCoeDecl(v_env_4620_, v_declName_4621_);
                    if v___x_4622_ == 0 {
                        crate::leanh::lean_dec(v_declName_4621_);
                        crate::leanh::lean_dec_ref(v_e_4605_);
                        v___y_4613_ = v___y_4606_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_4621_);
                        crate::leanh::lean_inc_ref(v_e_4605_);
                        v___x_4623_ = l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget(
                            v_e_4605_,
                            v_declName_4621_,
                            v___y_4607_,
                            v___y_4608_,
                            v___y_4609_,
                            v___y_4610_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4623_) == 0 {
                            v_a_4624_ = crate::leanh::lean_ctor_get(v___x_4623_, 0);
                            crate::leanh::lean_inc(v_a_4624_);
                            crate::leanh::lean_dec_ref_known(v___x_4623_, 1);
                            v___x_4625_ = 0;
                            v___x_4626_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0(v_a_4624_, v___x_4625_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
                            if crate::leanh::lean_obj_tag(v___x_4626_) == 0 {
                                v_a_4627_ = crate::leanh::lean_ctor_get(v___x_4626_, 0);
                                crate::leanh::lean_inc(v_a_4627_);
                                crate::leanh::lean_dec_ref_known(v___x_4626_, 1);
                                v_snd_4628_ = crate::leanh::lean_ctor_get(v_a_4627_, 1);
                                v_isSharedCheck_4679_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_4627_)) as u8;
                                if v_isSharedCheck_4679_ == 0 {
                                    v_unused_4680_ = crate::leanh::lean_ctor_get(v_a_4627_, 0);
                                    crate::leanh::lean_dec(v_unused_4680_);
                                    v___x_4630_ = v_a_4627_;
                                    v_isShared_4631_ = v_isSharedCheck_4679_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_4628_);
                                    crate::leanh::lean_dec(v_a_4627_);
                                    v___x_4630_ = crate::leanh::lean_box(0);
                                    v_isShared_4631_ = v_isSharedCheck_4679_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_declName_4621_);
                                crate::leanh::lean_dec_ref(v_e_4605_);
                                v_a_4681_ = crate::leanh::lean_ctor_get(v___x_4626_, 0);
                                v_isSharedCheck_4688_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4626_)) as u8;
                                if v_isSharedCheck_4688_ == 0 {
                                    v___x_4683_ = v___x_4626_;
                                    v_isShared_4684_ = v_isSharedCheck_4688_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4681_);
                                    crate::leanh::lean_dec(v___x_4626_);
                                    v___x_4683_ = crate::leanh::lean_box(0);
                                    v_isShared_4684_ = v_isSharedCheck_4688_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_4621_);
                            crate::leanh::lean_dec(v___y_4606_);
                            crate::leanh::lean_dec_ref(v_e_4605_);
                            v_a_4689_ = crate::leanh::lean_ctor_get(v___x_4623_, 0);
                            v_isSharedCheck_4696_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4623_)) as u8;
                            if v_isSharedCheck_4696_ == 0 {
                                v___x_4691_ = v___x_4623_;
                                v_isShared_4692_ = v_isSharedCheck_4696_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4689_);
                                crate::leanh::lean_dec(v___x_4623_);
                                v___x_4691_ = crate::leanh::lean_box(0);
                                v_isShared_4692_ = v_isSharedCheck_4696_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4614_ = l_Lean_Meta_expandCoe___lam__1___closed__0;
                v___x_4615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4615_, 0, v___x_4614_);
                crate::leanh::lean_ctor_set(v___x_4615_, 1, v___y_4613_);
                v___x_4616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4616_, 0, v___x_4615_);
                return v___x_4616_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_e_4605_);
                v___x_4632_ = l_Lean_Meta_unfoldDefinition_x3f(
                    v_e_4605_,
                    v___x_4625_,
                    v___y_4607_,
                    v___y_4608_,
                    v___y_4609_,
                    v___y_4610_,
                );
                if crate::leanh::lean_obj_tag(v___x_4632_) == 0 {
                    v_a_4633_ = crate::leanh::lean_ctor_get(v___x_4632_, 0);
                    v_isSharedCheck_4670_ = (!crate::leanh::lean_is_exclusive(v___x_4632_)) as u8;
                    if v_isSharedCheck_4670_ == 0 {
                        v___x_4635_ = v___x_4632_;
                        v_isShared_4636_ = v_isSharedCheck_4670_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4633_);
                        crate::leanh::lean_dec(v___x_4632_);
                        v___x_4635_ = crate::leanh::lean_box(0);
                        v_isShared_4636_ = v_isSharedCheck_4670_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4630_);
                    crate::leanh::lean_dec(v_snd_4628_);
                    crate::leanh::lean_dec(v_declName_4621_);
                    crate::leanh::lean_dec_ref(v_e_4605_);
                    v_a_4671_ = crate::leanh::lean_ctor_get(v___x_4632_, 0);
                    v_isSharedCheck_4678_ = (!crate::leanh::lean_is_exclusive(v___x_4632_)) as u8;
                    if v_isSharedCheck_4678_ == 0 {
                        v___x_4673_ = v___x_4632_;
                        v_isShared_4674_ = v_isSharedCheck_4678_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4671_);
                        crate::leanh::lean_dec(v___x_4632_);
                        v___x_4673_ = crate::leanh::lean_box(0);
                        v_isShared_4674_ = v_isSharedCheck_4678_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_4633_) == 1 {
                    v_val_4637_ = crate::leanh::lean_ctor_get(v_a_4633_, 0);
                    v_isSharedCheck_4669_ = (!crate::leanh::lean_is_exclusive(v_a_4633_)) as u8;
                    if v_isSharedCheck_4669_ == 0 {
                        v___x_4639_ = v_a_4633_;
                        v_isShared_4640_ = v_isSharedCheck_4669_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4637_);
                        crate::leanh::lean_dec(v_a_4633_);
                        v___x_4639_ = crate::leanh::lean_box(0);
                        v_isShared_4640_ = v_isSharedCheck_4669_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4635_);
                    crate::leanh::lean_dec(v_a_4633_);
                    crate::leanh::lean_del_object(v___x_4630_);
                    crate::leanh::lean_dec(v_declName_4621_);
                    crate::leanh::lean_dec_ref(v_e_4605_);
                    v___y_4613_ = v_snd_4628_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_4653_ = l_Lean_Meta_expandCoe___lam__1___closed__3;
                v___x_4654_ = lean_name_eq(v_declName_4621_, v___x_4653_);
                crate::leanh::lean_dec(v_declName_4621_);
                if v___x_4654_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_4605_);
                    v___y_4642_ = v_snd_4628_;
                    state = 5;
                    continue;
                } else {
                    v_dummy_4655_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once
                        ),
                        _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0,
                    );
                    v_nargs_4656_ = l_Lean_Expr_getAppNumArgs(v_e_4605_);
                    crate::leanh::lean_inc(v_nargs_4656_);
                    v___x_4657_ = lean_mk_array(v_nargs_4656_, v_dummy_4655_);
                    v___x_4658_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4659_ = lean_nat_sub(v_nargs_4656_, v___x_4658_);
                    crate::leanh::lean_dec(v_nargs_4656_);
                    v___x_4660_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_4605_,
                        v___x_4657_,
                        v___x_4659_,
                    );
                    v___x_4661_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4662_ = lean_array_get_size(v___x_4660_);
                    v___x_4663_ = lean_nat_dec_lt(v___x_4661_, v___x_4662_);
                    if v___x_4663_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4660_);
                        v___y_4642_ = v_snd_4628_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4664_ = lean_array_fget(v___x_4660_, v___x_4661_);
                        crate::leanh::lean_dec_ref(v___x_4660_);
                        v___x_4665_ = l_Lean_Expr_getAppFn(v___x_4664_);
                        crate::leanh::lean_dec(v___x_4664_);
                        v___x_4666_ = l_Lean_Expr_isConst(v___x_4665_);
                        if v___x_4666_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4665_);
                            v___y_4642_ = v_snd_4628_;
                            state = 5;
                            continue;
                        } else {
                            v___x_4667_ = l_Lean_Expr_constName_x21(v___x_4665_);
                            crate::leanh::lean_dec_ref(v___x_4665_);
                            v___x_4668_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4668_, 0, v___x_4667_);
                            crate::leanh::lean_ctor_set(v___x_4668_, 1, v_snd_4628_);
                            v___y_4642_ = v___x_4668_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_4643_ = l_Lean_Expr_headBeta(v_val_4637_);
                if v_isShared_4640_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4639_, 0, v___x_4643_);
                    v___x_4645_ = v___x_4639_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4643_);
                    v___x_4645_ = v_reuseFailAlloc_4652_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4630_, 1, v___y_4642_);
                    crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4645_);
                    v___x_4647_ = v___x_4630_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 1, v___y_4642_);
                    v___x_4647_ = v_reuseFailAlloc_4651_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4635_, 0, v___x_4647_);
                    v___x_4649_ = v___x_4635_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4647_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4649_;
            }
            9 => {
                if v_isShared_4674_ == 0 {
                    v___x_4676_ = v___x_4673_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
                    v___x_4676_ = v_reuseFailAlloc_4677_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4676_;
            }
            11 => {
                if v_isShared_4684_ == 0 {
                    v___x_4686_ = v___x_4683_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
                    v___x_4686_ = v_reuseFailAlloc_4687_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4686_;
            }
            13 => {
                if v_isShared_4692_ == 0 {
                    v___x_4694_ = v___x_4691_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
                    v___x_4694_ = v_reuseFailAlloc_4695_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_expandCoe___lam__1___boxed(
    mut v_e_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
    mut v___y_4700_: *mut crate::leanh::LeanObject,
    mut v___y_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4704_ = l_Lean_Meta_expandCoe___lam__1(
        v_e_4697_,
        v___y_4698_,
        v___y_4699_,
        v___y_4700_,
        v___y_4701_,
        v___y_4702_,
    );
    crate::leanh::lean_dec(v___y_4702_);
    crate::leanh::lean_dec_ref(v___y_4701_);
    crate::leanh::lean_dec(v___y_4700_);
    crate::leanh::lean_dec_ref(v___y_4699_);
    return v_res_4704_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(
    mut v_k_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v_b_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4712_);
    crate::leanh::lean_inc_ref(v___y_4711_);
    crate::leanh::lean_inc(v___y_4710_);
    crate::leanh::lean_inc_ref(v___y_4709_);
    crate::leanh::lean_inc(v___y_4706_);
    v___x_4714_ = crate::leanh::lean_apply_8(
        v_k_4705_,
        v_b_4708_,
        v___y_4706_,
        v___y_4707_,
        v___y_4709_,
        v___y_4710_,
        v___y_4711_,
        v___y_4712_,
        crate::leanh::lean_box(0),
    );
    return v___x_4714_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed(
    mut v_k_4715_: *mut crate::leanh::LeanObject,
    mut v___y_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v_b_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0(v_k_4715_, v___y_4716_, v___y_4717_, v_b_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
    crate::leanh::lean_dec(v___y_4722_);
    crate::leanh::lean_dec_ref(v___y_4721_);
    crate::leanh::lean_dec(v___y_4720_);
    crate::leanh::lean_dec_ref(v___y_4719_);
    crate::leanh::lean_dec(v___y_4716_);
    return v_res_4724_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(
    mut v_name_4725_: *mut crate::leanh::LeanObject,
    mut v_bi_4726_: u8,
    mut v_type_4727_: *mut crate::leanh::LeanObject,
    mut v_k_4728_: *mut crate::leanh::LeanObject,
    mut v_kind_4729_: u8,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
    mut v___y_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut v_a_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4730_);
                v___f_4737_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_4737_, 0, v_k_4728_);
                crate::leanh::lean_closure_set(v___f_4737_, 1, v___y_4730_);
                crate::leanh::lean_closure_set(v___f_4737_, 2, v___y_4731_);
                v___x_4738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4725_,
                    v_bi_4726_,
                    v_type_4727_,
                    v___f_4737_,
                    v_kind_4729_,
                    v___y_4732_,
                    v___y_4733_,
                    v___y_4734_,
                    v___y_4735_,
                );
                if crate::leanh::lean_obj_tag(v___x_4738_) == 0 {
                    v_a_4739_ = crate::leanh::lean_ctor_get(v___x_4738_, 0);
                    v_isSharedCheck_4746_ = (!crate::leanh::lean_is_exclusive(v___x_4738_)) as u8;
                    if v_isSharedCheck_4746_ == 0 {
                        v___x_4741_ = v___x_4738_;
                        v_isShared_4742_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4739_);
                        crate::leanh::lean_dec(v___x_4738_);
                        v___x_4741_ = crate::leanh::lean_box(0);
                        v_isShared_4742_ = v_isSharedCheck_4746_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4747_ = crate::leanh::lean_ctor_get(v___x_4738_, 0);
                    v_isSharedCheck_4754_ = (!crate::leanh::lean_is_exclusive(v___x_4738_)) as u8;
                    if v_isSharedCheck_4754_ == 0 {
                        v___x_4749_ = v___x_4738_;
                        v_isShared_4750_ = v_isSharedCheck_4754_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4747_);
                        crate::leanh::lean_dec(v___x_4738_);
                        v___x_4749_ = crate::leanh::lean_box(0);
                        v_isShared_4750_ = v_isSharedCheck_4754_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4742_ == 0 {
                    v___x_4744_ = v___x_4741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4739_);
                    v___x_4744_ = v_reuseFailAlloc_4745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4744_;
            }
            3 => {
                if v_isShared_4750_ == 0 {
                    v___x_4752_ = v___x_4749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
                    v___x_4752_ = v_reuseFailAlloc_4753_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___boxed(
    mut v_name_4755_: *mut crate::leanh::LeanObject,
    mut v_bi_4756_: *mut crate::leanh::LeanObject,
    mut v_type_4757_: *mut crate::leanh::LeanObject,
    mut v_k_4758_: *mut crate::leanh::LeanObject,
    mut v_kind_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
    mut v___y_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4767_: u8 = 0;
    let mut v_kind_boxed_4768_: u8 = 0;
    let mut v_res_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4767_ = (crate::leanh::lean_unbox(v_bi_4756_) as u8);
    v_kind_boxed_4768_ = (crate::leanh::lean_unbox(v_kind_4759_) as u8);
    v_res_4769_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_4755_, v_bi_boxed_4767_, v_type_4757_, v_k_4758_, v_kind_boxed_4768_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
    crate::leanh::lean_dec(v___y_4765_);
    crate::leanh::lean_dec_ref(v___y_4764_);
    crate::leanh::lean_dec(v___y_4763_);
    crate::leanh::lean_dec_ref(v___y_4762_);
    crate::leanh::lean_dec(v___y_4760_);
    return v_res_4769_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(
    mut v___x_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
    mut v___y_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4777_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4777_, 0, v___x_4770_);
    crate::leanh::lean_ctor_set(v___x_4777_, 1, v___y_4771_);
    v___x_4778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4778_, 0, v___x_4777_);
    return v___x_4778_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed(
    mut v___x_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4786_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2(v___x_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
    crate::leanh::lean_dec(v___y_4784_);
    crate::leanh::lean_dec_ref(v___y_4783_);
    crate::leanh::lean_dec(v___y_4782_);
    crate::leanh::lean_dec_ref(v___y_4781_);
    return v_res_4786_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(
    mut v_name_4787_: *mut crate::leanh::LeanObject,
    mut v_type_4788_: *mut crate::leanh::LeanObject,
    mut v_val_4789_: *mut crate::leanh::LeanObject,
    mut v_k_4790_: *mut crate::leanh::LeanObject,
    mut v_nondep_4791_: u8,
    mut v_kind_4792_: u8,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_a_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4793_);
                v___f_4800_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_4800_, 0, v_k_4790_);
                crate::leanh::lean_closure_set(v___f_4800_, 1, v___y_4793_);
                crate::leanh::lean_closure_set(v___f_4800_, 2, v___y_4794_);
                v___x_4801_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4787_,
                    v_type_4788_,
                    v_val_4789_,
                    v___f_4800_,
                    v_nondep_4791_,
                    v_kind_4792_,
                    v___y_4795_,
                    v___y_4796_,
                    v___y_4797_,
                    v___y_4798_,
                );
                if crate::leanh::lean_obj_tag(v___x_4801_) == 0 {
                    v_a_4802_ = crate::leanh::lean_ctor_get(v___x_4801_, 0);
                    v_isSharedCheck_4809_ = (!crate::leanh::lean_is_exclusive(v___x_4801_)) as u8;
                    if v_isSharedCheck_4809_ == 0 {
                        v___x_4804_ = v___x_4801_;
                        v_isShared_4805_ = v_isSharedCheck_4809_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4802_);
                        crate::leanh::lean_dec(v___x_4801_);
                        v___x_4804_ = crate::leanh::lean_box(0);
                        v_isShared_4805_ = v_isSharedCheck_4809_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4810_ = crate::leanh::lean_ctor_get(v___x_4801_, 0);
                    v_isSharedCheck_4817_ = (!crate::leanh::lean_is_exclusive(v___x_4801_)) as u8;
                    if v_isSharedCheck_4817_ == 0 {
                        v___x_4812_ = v___x_4801_;
                        v_isShared_4813_ = v_isSharedCheck_4817_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4810_);
                        crate::leanh::lean_dec(v___x_4801_);
                        v___x_4812_ = crate::leanh::lean_box(0);
                        v_isShared_4813_ = v_isSharedCheck_4817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4805_ == 0 {
                    v___x_4807_ = v___x_4804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
                    v___x_4807_ = v_reuseFailAlloc_4808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4807_;
            }
            3 => {
                if v_isShared_4813_ == 0 {
                    v___x_4815_ = v___x_4812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg___boxed(
    mut v_name_4818_: *mut crate::leanh::LeanObject,
    mut v_type_4819_: *mut crate::leanh::LeanObject,
    mut v_val_4820_: *mut crate::leanh::LeanObject,
    mut v_k_4821_: *mut crate::leanh::LeanObject,
    mut v_nondep_4822_: *mut crate::leanh::LeanObject,
    mut v_kind_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_4831_: u8 = 0;
    let mut v_kind_boxed_4832_: u8 = 0;
    let mut v_res_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4831_ = (crate::leanh::lean_unbox(v_nondep_4822_) as u8);
    v_kind_boxed_4832_ = (crate::leanh::lean_unbox(v_kind_4823_) as u8);
    v_res_4833_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_4818_, v_type_4819_, v_val_4820_, v_k_4821_, v_nondep_boxed_4831_, v_kind_boxed_4832_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
    crate::leanh::lean_dec(v___y_4829_);
    crate::leanh::lean_dec_ref(v___y_4828_);
    crate::leanh::lean_dec(v___y_4827_);
    crate::leanh::lean_dec_ref(v___y_4826_);
    crate::leanh::lean_dec(v___y_4824_);
    return v_res_4833_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(
    mut v_a_4834_: *mut crate::leanh::LeanObject,
    mut v_b_4835_: *mut crate::leanh::LeanObject,
    mut v_x_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4843_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4836_) == 0 {
                    crate::leanh::lean_dec(v_b_4835_);
                    crate::leanh::lean_dec_ref(v_a_4834_);
                    return v_x_4836_;
                } else {
                    v_key_4837_ = crate::leanh::lean_ctor_get(v_x_4836_, 0);
                    v_value_4838_ = crate::leanh::lean_ctor_get(v_x_4836_, 1);
                    v_tail_4839_ = crate::leanh::lean_ctor_get(v_x_4836_, 2);
                    v_isSharedCheck_4851_ = (!crate::leanh::lean_is_exclusive(v_x_4836_)) as u8;
                    if v_isSharedCheck_4851_ == 0 {
                        v___x_4841_ = v_x_4836_;
                        v_isShared_4842_ = v_isSharedCheck_4851_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4839_);
                        crate::leanh::lean_inc(v_value_4838_);
                        crate::leanh::lean_inc(v_key_4837_);
                        crate::leanh::lean_dec(v_x_4836_);
                        v___x_4841_ = crate::leanh::lean_box(0);
                        v_isShared_4842_ = v_isSharedCheck_4851_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4843_ = l_Lean_ExprStructEq_beq(v_key_4837_, v_a_4834_);
                if v___x_4843_ == 0 {
                    v___x_4844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_4834_, v_b_4835_, v_tail_4839_);
                    if v_isShared_4842_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4841_, 2, v___x_4844_);
                        v___x_4846_ = v___x_4841_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4847_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_key_4837_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 1, v_value_4838_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 2, v___x_4844_);
                        v___x_4846_ = v_reuseFailAlloc_4847_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4838_);
                    crate::leanh::lean_dec(v_key_4837_);
                    if v_isShared_4842_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4841_, 1, v_b_4835_);
                        crate::leanh::lean_ctor_set(v___x_4841_, 0, v_a_4834_);
                        v___x_4849_ = v___x_4841_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4850_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4834_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_b_4835_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 2, v_tail_4839_);
                        v___x_4849_ = v_reuseFailAlloc_4850_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4846_;
            }
            3 => {
                return v___x_4849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(
    mut v_a_4852_: *mut crate::leanh::LeanObject,
    mut v_x_4853_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4854_: u8 = 0;
    let mut v_key_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4853_) == 0 {
                    v___x_4854_ = 0;
                    return v___x_4854_;
                } else {
                    v_key_4855_ = crate::leanh::lean_ctor_get(v_x_4853_, 0);
                    v_tail_4856_ = crate::leanh::lean_ctor_get(v_x_4853_, 2);
                    v___x_4857_ = l_Lean_ExprStructEq_beq(v_key_4855_, v_a_4852_);
                    if v___x_4857_ == 0 {
                        v_x_4853_ = v_tail_4856_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4857_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg___boxed(
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_x_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4861_: u8 = 0;
    let mut v_r_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_4859_, v_x_4860_);
    crate::leanh::lean_dec(v_x_4860_);
    crate::leanh::lean_dec_ref(v_a_4859_);
    v_r_4862_ = crate::leanh::lean_box((v_res_4861_) as usize);
    return v_r_4862_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(
    mut v_x_4863_: *mut crate::leanh::LeanObject,
    mut v_x_4864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: u64 = 0;
    let mut v___x_4873_: u64 = 0;
    let mut v___x_4874_: u64 = 0;
    let mut v_fold_4875_: u64 = 0;
    let mut v___x_4876_: u64 = 0;
    let mut v___x_4877_: u64 = 0;
    let mut v___x_4878_: u64 = 0;
    let mut v___x_4879_: usize = 0;
    let mut v___x_4880_: usize = 0;
    let mut v___x_4881_: usize = 0;
    let mut v___x_4882_: usize = 0;
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4864_) == 0 {
                    return v_x_4863_;
                } else {
                    v_key_4865_ = crate::leanh::lean_ctor_get(v_x_4864_, 0);
                    v_value_4866_ = crate::leanh::lean_ctor_get(v_x_4864_, 1);
                    v_tail_4867_ = crate::leanh::lean_ctor_get(v_x_4864_, 2);
                    v_isSharedCheck_4890_ = (!crate::leanh::lean_is_exclusive(v_x_4864_)) as u8;
                    if v_isSharedCheck_4890_ == 0 {
                        v___x_4869_ = v_x_4864_;
                        v_isShared_4870_ = v_isSharedCheck_4890_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4867_);
                        crate::leanh::lean_inc(v_value_4866_);
                        crate::leanh::lean_inc(v_key_4865_);
                        crate::leanh::lean_dec(v_x_4864_);
                        v___x_4869_ = crate::leanh::lean_box(0);
                        v_isShared_4870_ = v_isSharedCheck_4890_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4871_ = lean_array_get_size(v_x_4863_);
                v___x_4872_ = l_Lean_ExprStructEq_hash(v_key_4865_);
                v___x_4873_ = 32u64;
                v___x_4874_ = lean_uint64_shift_right(v___x_4872_, v___x_4873_);
                v_fold_4875_ = lean_uint64_xor(v___x_4872_, v___x_4874_);
                v___x_4876_ = 16u64;
                v___x_4877_ = lean_uint64_shift_right(v_fold_4875_, v___x_4876_);
                v___x_4878_ = lean_uint64_xor(v_fold_4875_, v___x_4877_);
                v___x_4879_ = lean_uint64_to_usize(v___x_4878_);
                v___x_4880_ = lean_usize_of_nat(v___x_4871_);
                v___x_4881_ = 1usize;
                v___x_4882_ = lean_usize_sub(v___x_4880_, v___x_4881_);
                v___x_4883_ = lean_usize_land(v___x_4879_, v___x_4882_);
                v___x_4884_ = lean_array_uget_borrowed(v_x_4863_, v___x_4883_);
                crate::leanh::lean_inc(v___x_4884_);
                if v_isShared_4870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4869_, 2, v___x_4884_);
                    v___x_4886_ = v___x_4869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4889_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_key_4865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_value_4866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4889_, 2, v___x_4884_);
                    v___x_4886_ = v_reuseFailAlloc_4889_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4887_ = lean_array_uset(v_x_4863_, v___x_4883_, v___x_4886_);
                v_x_4863_ = v___x_4887_;
                v_x_4864_ = v_tail_4867_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(
    mut v_i_4891_: *mut crate::leanh::LeanObject,
    mut v_source_4892_: *mut crate::leanh::LeanObject,
    mut v_target_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: u8 = 0;
    let mut v_es_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4894_ = lean_array_get_size(v_source_4892_);
                v___x_4895_ = lean_nat_dec_lt(v_i_4891_, v___x_4894_);
                if v___x_4895_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4892_);
                    crate::leanh::lean_dec(v_i_4891_);
                    return v_target_4893_;
                } else {
                    v_es_4896_ = lean_array_fget(v_source_4892_, v_i_4891_);
                    v___x_4897_ = crate::leanh::lean_box(0);
                    v_source_4898_ = lean_array_fset(v_source_4892_, v_i_4891_, v___x_4897_);
                    v_target_4899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_target_4893_, v_es_4896_);
                    v___x_4900_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4901_ = lean_nat_add(v_i_4891_, v___x_4900_);
                    crate::leanh::lean_dec(v_i_4891_);
                    v_i_4891_ = v___x_4901_;
                    v_source_4892_ = v_source_4898_;
                    v_target_4893_ = v_target_4899_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(
    mut v_data_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4904_ = lean_array_get_size(v_data_4903_);
    v___x_4905_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4906_ = lean_nat_mul(v___x_4904_, v___x_4905_);
    v___x_4907_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4908_ = crate::leanh::lean_box(0);
    v___x_4909_ = lean_mk_array(v_nbuckets_4906_, v___x_4908_);
    v___x_4910_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v___x_4907_, v_data_4903_, v___x_4909_);
    return v___x_4910_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(
    mut v_m_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
    mut v_b_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: u64 = 0;
    let mut v___x_4921_: u64 = 0;
    let mut v___x_4922_: u64 = 0;
    let mut v_fold_4923_: u64 = 0;
    let mut v___x_4924_: u64 = 0;
    let mut v___x_4925_: u64 = 0;
    let mut v___x_4926_: u64 = 0;
    let mut v___x_4927_: usize = 0;
    let mut v___x_4928_: usize = 0;
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: usize = 0;
    let mut v___x_4931_: usize = 0;
    let mut v_bkt_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: u8 = 0;
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v_val_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4914_ = crate::leanh::lean_ctor_get(v_m_4911_, 0);
                v_buckets_4915_ = crate::leanh::lean_ctor_get(v_m_4911_, 1);
                v_isSharedCheck_4958_ = (!crate::leanh::lean_is_exclusive(v_m_4911_)) as u8;
                if v_isSharedCheck_4958_ == 0 {
                    v___x_4917_ = v_m_4911_;
                    v_isShared_4918_ = v_isSharedCheck_4958_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4915_);
                    crate::leanh::lean_inc(v_size_4914_);
                    crate::leanh::lean_dec(v_m_4911_);
                    v___x_4917_ = crate::leanh::lean_box(0);
                    v_isShared_4918_ = v_isSharedCheck_4958_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4919_ = lean_array_get_size(v_buckets_4915_);
                v___x_4920_ = l_Lean_ExprStructEq_hash(v_a_4912_);
                v___x_4921_ = 32u64;
                v___x_4922_ = lean_uint64_shift_right(v___x_4920_, v___x_4921_);
                v_fold_4923_ = lean_uint64_xor(v___x_4920_, v___x_4922_);
                v___x_4924_ = 16u64;
                v___x_4925_ = lean_uint64_shift_right(v_fold_4923_, v___x_4924_);
                v___x_4926_ = lean_uint64_xor(v_fold_4923_, v___x_4925_);
                v___x_4927_ = lean_uint64_to_usize(v___x_4926_);
                v___x_4928_ = lean_usize_of_nat(v___x_4919_);
                v___x_4929_ = 1usize;
                v___x_4930_ = lean_usize_sub(v___x_4928_, v___x_4929_);
                v___x_4931_ = lean_usize_land(v___x_4927_, v___x_4930_);
                v_bkt_4932_ = lean_array_uget_borrowed(v_buckets_4915_, v___x_4931_);
                v___x_4933_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_4912_, v_bkt_4932_);
                if v___x_4933_ == 0 {
                    v___x_4934_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4935_ = lean_nat_add(v_size_4914_, v___x_4934_);
                    crate::leanh::lean_dec(v_size_4914_);
                    crate::leanh::lean_inc(v_bkt_4932_);
                    v___x_4936_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4936_, 0, v_a_4912_);
                    crate::leanh::lean_ctor_set(v___x_4936_, 1, v_b_4913_);
                    crate::leanh::lean_ctor_set(v___x_4936_, 2, v_bkt_4932_);
                    v_buckets_x27_4937_ =
                        lean_array_uset(v_buckets_4915_, v___x_4931_, v___x_4936_);
                    v___x_4938_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4939_ = lean_nat_mul(v_size_x27_4935_, v___x_4938_);
                    v___x_4940_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4941_ = lean_nat_div(v___x_4939_, v___x_4940_);
                    crate::leanh::lean_dec(v___x_4939_);
                    v___x_4942_ = lean_array_get_size(v_buckets_x27_4937_);
                    v___x_4943_ = lean_nat_dec_le(v___x_4941_, v___x_4942_);
                    crate::leanh::lean_dec(v___x_4941_);
                    if v___x_4943_ == 0 {
                        v_val_4944_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_buckets_x27_4937_);
                        if v_isShared_4918_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4917_, 1, v_val_4944_);
                            crate::leanh::lean_ctor_set(v___x_4917_, 0, v_size_x27_4935_);
                            v___x_4946_ = v___x_4917_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4947_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4947_,
                                0,
                                v_size_x27_4935_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 1, v_val_4944_);
                            v___x_4946_ = v_reuseFailAlloc_4947_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4918_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4917_, 1, v_buckets_x27_4937_);
                            crate::leanh::lean_ctor_set(v___x_4917_, 0, v_size_x27_4935_);
                            v___x_4949_ = v___x_4917_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4950_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4950_,
                                0,
                                v_size_x27_4935_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4950_,
                                1,
                                v_buckets_x27_4937_,
                            );
                            v___x_4949_ = v_reuseFailAlloc_4950_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4932_);
                    v___x_4951_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4952_ =
                        lean_array_uset(v_buckets_4915_, v___x_4931_, v___x_4951_);
                    v___x_4953_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_4912_, v_b_4913_, v_bkt_4932_);
                    v___x_4954_ = lean_array_uset(v_buckets_x27_4952_, v___x_4931_, v___x_4953_);
                    if v_isShared_4918_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4917_, 1, v___x_4954_);
                        v___x_4956_ = v___x_4917_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_size_4914_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4957_, 1, v___x_4954_);
                        v___x_4956_ = v_reuseFailAlloc_4957_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4946_;
            }
            3 => {
                return v___x_4949_;
            }
            4 => {
                return v___x_4956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(
    mut v_a_4959_: *mut crate::leanh::LeanObject,
    mut v_e_4960_: *mut crate::leanh::LeanObject,
    mut v_fst_4961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4963_ = lean_st_ref_take(v_a_4959_);
    v___x_4964_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v___x_4963_, v_e_4960_, v_fst_4961_);
    v___x_4965_ = lean_st_ref_set(v_a_4959_, v___x_4964_);
    v___x_4966_ = crate::leanh::lean_box(0);
    return v___x_4966_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed(
    mut v_a_4967_: *mut crate::leanh::LeanObject,
    mut v_e_4968_: *mut crate::leanh::LeanObject,
    mut v_fst_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2(v_a_4967_, v_e_4968_, v_fst_4969_);
    crate::leanh::lean_dec(v_a_4967_);
    return v_res_4971_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4977_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4978_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4978_, 0, v___x_4977_);
    return v___x_4978_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4979_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__3);
    v___x_4980_ = l_Lean_MessageData_ofFormat(v___x_4979_);
    return v___x_4980_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__4);
    v___x_4982_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__2;
    v___x_4983_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4983_, 0, v___x_4982_);
    crate::leanh::lean_ctor_set(v___x_4983_, 1, v___x_4981_);
    return v___x_4983_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(
    mut v_ref_4984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___closed__5);
    v___x_4987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4987_, 0, v_ref_4984_);
    crate::leanh::lean_ctor_set(v___x_4987_, 1, v___x_4986_);
    v___x_4988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4988_, 0, v___x_4987_);
    return v___x_4988_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg___boxed(
    mut v_ref_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4991_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_4989_);
    return v_res_4991_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(
    mut v_x_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5005_: u8 = 0;
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v_a_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_fileName_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5030_: u8 = 0;
    let mut v_cancelTk_x3f_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5032_: u8 = 0;
    let mut v_inheritedTraceOptions_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: u8 = 0;
    let mut v___x_5041_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5018_ = crate::leanh::lean_ctor_get(v___y_4997_, 0);
                v_fileMap_5019_ = crate::leanh::lean_ctor_get(v___y_4997_, 1);
                v_options_5020_ = crate::leanh::lean_ctor_get(v___y_4997_, 2);
                v_currRecDepth_5021_ = crate::leanh::lean_ctor_get(v___y_4997_, 3);
                v_maxRecDepth_5022_ = crate::leanh::lean_ctor_get(v___y_4997_, 4);
                v_ref_5023_ = crate::leanh::lean_ctor_get(v___y_4997_, 5);
                v_currNamespace_5024_ = crate::leanh::lean_ctor_get(v___y_4997_, 6);
                v_openDecls_5025_ = crate::leanh::lean_ctor_get(v___y_4997_, 7);
                v_initHeartbeats_5026_ = crate::leanh::lean_ctor_get(v___y_4997_, 8);
                v_maxHeartbeats_5027_ = crate::leanh::lean_ctor_get(v___y_4997_, 9);
                v_quotContext_5028_ = crate::leanh::lean_ctor_get(v___y_4997_, 10);
                v_currMacroScope_5029_ = crate::leanh::lean_ctor_get(v___y_4997_, 11);
                v_diag_5030_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4997_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5031_ = crate::leanh::lean_ctor_get(v___y_4997_, 12);
                v_suppressElabErrors_5032_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4997_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5033_ = crate::leanh::lean_ctor_get(v___y_4997_, 13);
                v___x_5039_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5040_ = lean_nat_dec_eq(v_maxRecDepth_5022_, v___x_5039_);
                if v___x_5040_ == 0 {
                    v___x_5041_ = lean_nat_dec_eq(v_currRecDepth_5021_, v_maxRecDepth_5022_);
                    if v___x_5041_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_4994_);
                        crate::leanh::lean_dec_ref(v_x_4992_);
                        crate::leanh::lean_inc(v_ref_5023_);
                        v___x_5042_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_5023_);
                        v___y_5001_ = v___x_5042_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 6;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5001_) == 0 {
                    v_a_5002_ = crate::leanh::lean_ctor_get(v___y_5001_, 0);
                    v_isSharedCheck_5009_ = (!crate::leanh::lean_is_exclusive(v___y_5001_)) as u8;
                    if v_isSharedCheck_5009_ == 0 {
                        v___x_5004_ = v___y_5001_;
                        v_isShared_5005_ = v_isSharedCheck_5009_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5002_);
                        crate::leanh::lean_dec(v___y_5001_);
                        v___x_5004_ = crate::leanh::lean_box(0);
                        v_isShared_5005_ = v_isSharedCheck_5009_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5010_ = crate::leanh::lean_ctor_get(v___y_5001_, 0);
                    v_isSharedCheck_5017_ = (!crate::leanh::lean_is_exclusive(v___y_5001_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_5012_ = v___y_5001_;
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5010_);
                        crate::leanh::lean_dec(v___y_5001_);
                        v___x_5012_ = crate::leanh::lean_box(0);
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5005_ == 0 {
                    v___x_5007_ = v___x_5004_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
                    v___x_5007_ = v_reuseFailAlloc_5008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5007_;
            }
            4 => {
                if v_isShared_5013_ == 0 {
                    v___x_5015_ = v___x_5012_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
                    v___x_5015_ = v_reuseFailAlloc_5016_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5015_;
            }
            6 => {
                v___x_5035_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5036_ = lean_nat_add(v_currRecDepth_5021_, v___x_5035_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5033_);
                crate::leanh::lean_inc(v_cancelTk_x3f_5031_);
                crate::leanh::lean_inc(v_currMacroScope_5029_);
                crate::leanh::lean_inc(v_quotContext_5028_);
                crate::leanh::lean_inc(v_maxHeartbeats_5027_);
                crate::leanh::lean_inc(v_initHeartbeats_5026_);
                crate::leanh::lean_inc(v_openDecls_5025_);
                crate::leanh::lean_inc(v_currNamespace_5024_);
                crate::leanh::lean_inc(v_ref_5023_);
                crate::leanh::lean_inc(v_maxRecDepth_5022_);
                crate::leanh::lean_inc_ref(v_options_5020_);
                crate::leanh::lean_inc_ref(v_fileMap_5019_);
                crate::leanh::lean_inc_ref(v_fileName_5018_);
                v___x_5037_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5037_, 0, v_fileName_5018_);
                crate::leanh::lean_ctor_set(v___x_5037_, 1, v_fileMap_5019_);
                crate::leanh::lean_ctor_set(v___x_5037_, 2, v_options_5020_);
                crate::leanh::lean_ctor_set(v___x_5037_, 3, v___x_5036_);
                crate::leanh::lean_ctor_set(v___x_5037_, 4, v_maxRecDepth_5022_);
                crate::leanh::lean_ctor_set(v___x_5037_, 5, v_ref_5023_);
                crate::leanh::lean_ctor_set(v___x_5037_, 6, v_currNamespace_5024_);
                crate::leanh::lean_ctor_set(v___x_5037_, 7, v_openDecls_5025_);
                crate::leanh::lean_ctor_set(v___x_5037_, 8, v_initHeartbeats_5026_);
                crate::leanh::lean_ctor_set(v___x_5037_, 9, v_maxHeartbeats_5027_);
                crate::leanh::lean_ctor_set(v___x_5037_, 10, v_quotContext_5028_);
                crate::leanh::lean_ctor_set(v___x_5037_, 11, v_currMacroScope_5029_);
                crate::leanh::lean_ctor_set(v___x_5037_, 12, v_cancelTk_x3f_5031_);
                crate::leanh::lean_ctor_set(v___x_5037_, 13, v_inheritedTraceOptions_5033_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5037_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_5030_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5037_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5032_,
                );
                crate::leanh::lean_inc(v___y_4998_);
                crate::leanh::lean_inc(v___y_4996_);
                crate::leanh::lean_inc_ref(v___y_4995_);
                crate::leanh::lean_inc(v___y_4993_);
                v___x_5038_ = crate::leanh::lean_apply_7(
                    v_x_4992_,
                    v___y_4993_,
                    v___y_4994_,
                    v___y_4995_,
                    v___y_4996_,
                    v___x_5037_,
                    v___y_4998_,
                    crate::leanh::lean_box(0),
                );
                v___y_5001_ = v___x_5038_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg___boxed(
    mut v_x_5043_: *mut crate::leanh::LeanObject,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5051_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_);
    crate::leanh::lean_dec(v___y_5049_);
    crate::leanh::lean_dec_ref(v___y_5048_);
    crate::leanh::lean_dec(v___y_5047_);
    crate::leanh::lean_dec_ref(v___y_5046_);
    crate::leanh::lean_dec(v___y_5044_);
    return v_res_5051_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(
    mut v_a_5052_: *mut crate::leanh::LeanObject,
    mut v_x_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5053_) == 0 {
                    v___x_5054_ = crate::leanh::lean_box(0);
                    return v___x_5054_;
                } else {
                    v_key_5055_ = crate::leanh::lean_ctor_get(v_x_5053_, 0);
                    v_value_5056_ = crate::leanh::lean_ctor_get(v_x_5053_, 1);
                    v_tail_5057_ = crate::leanh::lean_ctor_get(v_x_5053_, 2);
                    v___x_5058_ = l_Lean_ExprStructEq_beq(v_key_5055_, v_a_5052_);
                    if v___x_5058_ == 0 {
                        v_x_5053_ = v_tail_5057_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5056_);
                        v___x_5060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5060_, 0, v_value_5056_);
                        return v___x_5060_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg___boxed(
    mut v_a_5061_: *mut crate::leanh::LeanObject,
    mut v_x_5062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_5061_, v_x_5062_);
    crate::leanh::lean_dec(v_x_5062_);
    crate::leanh::lean_dec_ref(v_a_5061_);
    return v_res_5063_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(
    mut v_m_5064_: *mut crate::leanh::LeanObject,
    mut v_a_5065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: u64 = 0;
    let mut v___x_5069_: u64 = 0;
    let mut v___x_5070_: u64 = 0;
    let mut v_fold_5071_: u64 = 0;
    let mut v___x_5072_: u64 = 0;
    let mut v___x_5073_: u64 = 0;
    let mut v___x_5074_: u64 = 0;
    let mut v___x_5075_: usize = 0;
    let mut v___x_5076_: usize = 0;
    let mut v___x_5077_: usize = 0;
    let mut v___x_5078_: usize = 0;
    let mut v___x_5079_: usize = 0;
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5066_ = crate::leanh::lean_ctor_get(v_m_5064_, 1);
    v___x_5067_ = lean_array_get_size(v_buckets_5066_);
    v___x_5068_ = l_Lean_ExprStructEq_hash(v_a_5065_);
    v___x_5069_ = 32u64;
    v___x_5070_ = lean_uint64_shift_right(v___x_5068_, v___x_5069_);
    v_fold_5071_ = lean_uint64_xor(v___x_5068_, v___x_5070_);
    v___x_5072_ = 16u64;
    v___x_5073_ = lean_uint64_shift_right(v_fold_5071_, v___x_5072_);
    v___x_5074_ = lean_uint64_xor(v_fold_5071_, v___x_5073_);
    v___x_5075_ = lean_uint64_to_usize(v___x_5074_);
    v___x_5076_ = lean_usize_of_nat(v___x_5067_);
    v___x_5077_ = 1usize;
    v___x_5078_ = lean_usize_sub(v___x_5076_, v___x_5077_);
    v___x_5079_ = lean_usize_land(v___x_5075_, v___x_5078_);
    v___x_5080_ = lean_array_uget_borrowed(v_buckets_5066_, v___x_5079_);
    v___x_5081_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_5065_, v___x_5080_);
    return v___x_5081_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg___boxed(
    mut v_m_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_5082_, v_a_5083_);
    crate::leanh::lean_dec_ref(v_a_5083_);
    crate::leanh::lean_dec_ref(v_m_5082_);
    return v_res_5084_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(
    mut v_00_u03b1_5085_: *mut crate::leanh::LeanObject,
    mut v_x_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
    mut v___y_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5093_ = crate::leanh::lean_apply_1(v_x_5086_, crate::leanh::lean_box(0));
    v___x_5094_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5094_, 0, v___x_5093_);
    crate::leanh::lean_ctor_set(v___x_5094_, 1, v___y_5087_);
    v___x_5095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5095_, 0, v___x_5094_);
    return v___x_5095_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0___boxed(
    mut v_00_u03b1_5096_: *mut crate::leanh::LeanObject,
    mut v_x_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5104_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(v_00_u03b1_5096_, v_x_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
    crate::leanh::lean_dec(v___y_5102_);
    crate::leanh::lean_dec_ref(v___y_5101_);
    crate::leanh::lean_dec(v___y_5100_);
    crate::leanh::lean_dec_ref(v___y_5099_);
    return v_res_5104_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(
    mut v_fvars_5108_: *mut crate::leanh::LeanObject,
    mut v_pre_5109_: *mut crate::leanh::LeanObject,
    mut v_post_5110_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5111_: u8,
    mut v_skipConstInApp_5112_: u8,
    mut v_skipInstances_5113_: u8,
    mut v_body_5114_: *mut crate::leanh::LeanObject,
    mut v_x_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5123_ = lean_array_push(v_fvars_5108_, v_x_5115_);
    v___x_5124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_5109_, v_post_5110_, v_usedLetOnly_5111_, v_skipConstInApp_5112_, v_skipInstances_5113_, v___x_5123_, v_body_5114_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
    return v___x_5124_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed(
    mut v_fvars_5125_: *mut crate::leanh::LeanObject,
    mut v_pre_5126_: *mut crate::leanh::LeanObject,
    mut v_post_5127_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5128_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5129_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5130_: *mut crate::leanh::LeanObject,
    mut v_body_5131_: *mut crate::leanh::LeanObject,
    mut v_x_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5140_: u8 = 0;
    let mut v_skipConstInApp_boxed_5141_: u8 = 0;
    let mut v_skipInstances_boxed_5142_: u8 = 0;
    let mut v_res_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5140_ = (crate::leanh::lean_unbox(v_usedLetOnly_5128_) as u8);
    v_skipConstInApp_boxed_5141_ = (crate::leanh::lean_unbox(v_skipConstInApp_5129_) as u8);
    v_skipInstances_boxed_5142_ = (crate::leanh::lean_unbox(v_skipInstances_5130_) as u8);
    v_res_5143_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0(v_fvars_5125_, v_pre_5126_, v_post_5127_, v_usedLetOnly_boxed_5140_, v_skipConstInApp_boxed_5141_, v_skipInstances_boxed_5142_, v_body_5131_, v_x_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
    crate::leanh::lean_dec(v___y_5138_);
    crate::leanh::lean_dec_ref(v___y_5137_);
    crate::leanh::lean_dec(v___y_5136_);
    crate::leanh::lean_dec_ref(v___y_5135_);
    crate::leanh::lean_dec(v___y_5133_);
    return v_res_5143_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(
    mut v_pre_5144_: *mut crate::leanh::LeanObject,
    mut v_post_5145_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5146_: u8,
    mut v_skipConstInApp_5147_: u8,
    mut v_skipInstances_5148_: u8,
    mut v_e_5149_: *mut crate::leanh::LeanObject,
    mut v_a_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v_fst_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___y_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5178_: u8 = 0;
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut v_e_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_isSharedCheck_5189_: u8 = 0;
    let mut v_a_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5193_: u8 = 0;
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_5145_);
                crate::leanh::lean_inc(v___y_5155_);
                crate::leanh::lean_inc_ref(v___y_5154_);
                crate::leanh::lean_inc(v___y_5153_);
                crate::leanh::lean_inc_ref(v___y_5152_);
                crate::leanh::lean_inc_ref(v_e_5149_);
                v___x_5157_ = crate::leanh::lean_apply_7(
                    v_post_5145_,
                    v_e_5149_,
                    v___y_5151_,
                    v___y_5152_,
                    v___y_5153_,
                    v___y_5154_,
                    v___y_5155_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5157_) == 0 {
                    v_a_5158_ = crate::leanh::lean_ctor_get(v___x_5157_, 0);
                    v_isSharedCheck_5189_ = (!crate::leanh::lean_is_exclusive(v___x_5157_)) as u8;
                    if v_isSharedCheck_5189_ == 0 {
                        v___x_5160_ = v___x_5157_;
                        v_isShared_5161_ = v_isSharedCheck_5189_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5158_);
                        crate::leanh::lean_dec(v___x_5157_);
                        v___x_5160_ = crate::leanh::lean_box(0);
                        v_isShared_5161_ = v_isSharedCheck_5189_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5149_);
                    crate::leanh::lean_dec_ref(v_post_5145_);
                    crate::leanh::lean_dec_ref(v_pre_5144_);
                    v_a_5190_ = crate::leanh::lean_ctor_get(v___x_5157_, 0);
                    v_isSharedCheck_5197_ = (!crate::leanh::lean_is_exclusive(v___x_5157_)) as u8;
                    if v_isSharedCheck_5197_ == 0 {
                        v___x_5192_ = v___x_5157_;
                        v_isShared_5193_ = v_isSharedCheck_5197_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5190_);
                        crate::leanh::lean_dec(v___x_5157_);
                        v___x_5192_ = crate::leanh::lean_box(0);
                        v_isShared_5193_ = v_isSharedCheck_5197_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5162_ = crate::leanh::lean_ctor_get(v_a_5158_, 0);
                v_snd_5163_ = crate::leanh::lean_ctor_get(v_a_5158_, 1);
                v_isSharedCheck_5188_ = (!crate::leanh::lean_is_exclusive(v_a_5158_)) as u8;
                if v_isSharedCheck_5188_ == 0 {
                    v___x_5165_ = v_a_5158_;
                    v_isShared_5166_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5163_);
                    crate::leanh::lean_inc(v_fst_5162_);
                    crate::leanh::lean_dec(v_a_5158_);
                    v___x_5165_ = crate::leanh::lean_box(0);
                    v_isShared_5166_ = v_isSharedCheck_5188_;
                    state = 2;
                    continue;
                }
            }
            2 => match crate::leanh::lean_obj_tag(v_fst_5162_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_5165_);
                    crate::leanh::lean_del_object(v___x_5160_);
                    crate::leanh::lean_dec_ref(v_e_5149_);
                    crate::leanh::lean_dec_ref(v_post_5145_);
                    crate::leanh::lean_dec_ref(v_pre_5144_);
                    v_e_5175_ = crate::leanh::lean_ctor_get(v_fst_5162_, 0);
                    v_isSharedCheck_5183_ = (!crate::leanh::lean_is_exclusive(v_fst_5162_)) as u8;
                    if v_isSharedCheck_5183_ == 0 {
                        v___x_5177_ = v_fst_5162_;
                        v_isShared_5178_ = v_isSharedCheck_5183_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_e_5175_);
                        crate::leanh::lean_dec(v_fst_5162_);
                        v___x_5177_ = crate::leanh::lean_box(0);
                        v_isShared_5178_ = v_isSharedCheck_5183_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_5165_);
                    crate::leanh::lean_del_object(v___x_5160_);
                    crate::leanh::lean_dec_ref(v_e_5149_);
                    v_e_5184_ = crate::leanh::lean_ctor_get(v_fst_5162_, 0);
                    crate::leanh::lean_inc_ref(v_e_5184_);
                    crate::leanh::lean_dec_ref_known(v_fst_5162_, 1);
                    v___x_5185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5144_, v_post_5145_, v_usedLetOnly_5146_, v_skipConstInApp_5147_, v_skipInstances_5148_, v_e_5184_, v_a_5150_, v_snd_5163_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
                    return v___x_5185_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_5145_);
                    crate::leanh::lean_dec_ref(v_pre_5144_);
                    v_e_x3f_5186_ = crate::leanh::lean_ctor_get(v_fst_5162_, 0);
                    crate::leanh::lean_inc(v_e_x3f_5186_);
                    crate::leanh::lean_dec_ref_known(v_fst_5162_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_5186_) == 0 {
                        v___y_5168_ = v_e_5149_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5149_);
                        v_val_5187_ = crate::leanh::lean_ctor_get(v_e_x3f_5186_, 0);
                        crate::leanh::lean_inc(v_val_5187_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_5186_, 1);
                        v___y_5168_ = v_val_5187_;
                        state = 3;
                        continue;
                    }
                }
            },
            3 => {
                if v_isShared_5166_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5165_, 0, v___y_5168_);
                    v___x_5170_ = v___x_5165_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5174_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___y_5168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5174_, 1, v_snd_5163_);
                    v___x_5170_ = v_reuseFailAlloc_5174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5170_);
                    v___x_5172_ = v___x_5160_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5170_);
                    v___x_5172_ = v_reuseFailAlloc_5173_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5172_;
            }
            6 => {
                v___x_5179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5179_, 0, v_e_5175_);
                crate::leanh::lean_ctor_set(v___x_5179_, 1, v_snd_5163_);
                if v_isShared_5178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5177_, 0, v___x_5179_);
                    v___x_5181_ = v___x_5177_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5179_);
                    v___x_5181_ = v_reuseFailAlloc_5182_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5181_;
            }
            8 => {
                if v_isShared_5193_ == 0 {
                    v___x_5195_ = v___x_5192_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
                    v___x_5195_ = v_reuseFailAlloc_5196_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(
    mut v_pre_5198_: *mut crate::leanh::LeanObject,
    mut v_post_5199_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5200_: u8,
    mut v_skipConstInApp_5201_: u8,
    mut v_skipInstances_5202_: u8,
    mut v_fvars_5203_: *mut crate::leanh::LeanObject,
    mut v_e_5204_: *mut crate::leanh::LeanObject,
    mut v_a_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5215_: u8 = 0;
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: u8 = 0;
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: u8 = 0;
    let mut v___x_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_5204_) == 6 {
                    v_binderName_5212_ = crate::leanh::lean_ctor_get(v_e_5204_, 0);
                    crate::leanh::lean_inc(v_binderName_5212_);
                    v_binderType_5213_ = crate::leanh::lean_ctor_get(v_e_5204_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5213_);
                    v_body_5214_ = crate::leanh::lean_ctor_get(v_e_5204_, 2);
                    crate::leanh::lean_inc_ref(v_body_5214_);
                    v_binderInfo_5215_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_5204_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_5204_, 3);
                    v___x_5216_ = lean_expr_instantiate_rev(v_binderType_5213_, v_fvars_5203_);
                    crate::leanh::lean_dec_ref(v_binderType_5213_);
                    crate::leanh::lean_inc_ref(v_post_5199_);
                    crate::leanh::lean_inc_ref(v_pre_5198_);
                    v___x_5217_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5198_, v_post_5199_, v_usedLetOnly_5200_, v_skipConstInApp_5201_, v_skipInstances_5202_, v___x_5216_, v_a_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
                    if crate::leanh::lean_obj_tag(v___x_5217_) == 0 {
                        v_a_5218_ = crate::leanh::lean_ctor_get(v___x_5217_, 0);
                        crate::leanh::lean_inc(v_a_5218_);
                        crate::leanh::lean_dec_ref_known(v___x_5217_, 1);
                        v_fst_5219_ = crate::leanh::lean_ctor_get(v_a_5218_, 0);
                        crate::leanh::lean_inc(v_fst_5219_);
                        v_snd_5220_ = crate::leanh::lean_ctor_get(v_a_5218_, 1);
                        crate::leanh::lean_inc(v_snd_5220_);
                        crate::leanh::lean_dec(v_a_5218_);
                        v___x_5221_ = crate::leanh::lean_box((v_usedLetOnly_5200_) as usize);
                        v___x_5222_ = crate::leanh::lean_box((v_skipConstInApp_5201_) as usize);
                        v___x_5223_ = crate::leanh::lean_box((v_skipInstances_5202_) as usize);
                        v___f_5224_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
                        crate::leanh::lean_closure_set(v___f_5224_, 0, v_fvars_5203_);
                        crate::leanh::lean_closure_set(v___f_5224_, 1, v_pre_5198_);
                        crate::leanh::lean_closure_set(v___f_5224_, 2, v_post_5199_);
                        crate::leanh::lean_closure_set(v___f_5224_, 3, v___x_5221_);
                        crate::leanh::lean_closure_set(v___f_5224_, 4, v___x_5222_);
                        crate::leanh::lean_closure_set(v___f_5224_, 5, v___x_5223_);
                        crate::leanh::lean_closure_set(v___f_5224_, 6, v_body_5214_);
                        v___x_5225_ = 0;
                        v___x_5226_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_5212_, v_binderInfo_5215_, v_fst_5219_, v___f_5224_, v___x_5225_, v_a_5205_, v_snd_5220_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
                        return v___x_5226_;
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5214_);
                        crate::leanh::lean_dec(v_binderName_5212_);
                        crate::leanh::lean_dec_ref(v_fvars_5203_);
                        crate::leanh::lean_dec_ref(v_post_5199_);
                        crate::leanh::lean_dec_ref(v_pre_5198_);
                        return v___x_5217_;
                    }
                } else {
                    v___x_5227_ = lean_expr_instantiate_rev(v_e_5204_, v_fvars_5203_);
                    crate::leanh::lean_dec_ref(v_e_5204_);
                    crate::leanh::lean_inc_ref(v_post_5199_);
                    crate::leanh::lean_inc_ref(v_pre_5198_);
                    v___x_5228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5198_, v_post_5199_, v_usedLetOnly_5200_, v_skipConstInApp_5201_, v_skipInstances_5202_, v___x_5227_, v_a_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
                    if crate::leanh::lean_obj_tag(v___x_5228_) == 0 {
                        v_a_5229_ = crate::leanh::lean_ctor_get(v___x_5228_, 0);
                        crate::leanh::lean_inc(v_a_5229_);
                        crate::leanh::lean_dec_ref_known(v___x_5228_, 1);
                        v_fst_5230_ = crate::leanh::lean_ctor_get(v_a_5229_, 0);
                        crate::leanh::lean_inc(v_fst_5230_);
                        v_snd_5231_ = crate::leanh::lean_ctor_get(v_a_5229_, 1);
                        crate::leanh::lean_inc(v_snd_5231_);
                        crate::leanh::lean_dec(v_a_5229_);
                        v___x_5232_ = 0;
                        v___x_5233_ = 1;
                        v___x_5234_ = 1;
                        v___x_5235_ = l_Lean_Meta_mkLambdaFVars(
                            v_fvars_5203_,
                            v_fst_5230_,
                            v___x_5232_,
                            v_usedLetOnly_5200_,
                            v___x_5232_,
                            v___x_5233_,
                            v___x_5234_,
                            v___y_5207_,
                            v___y_5208_,
                            v___y_5209_,
                            v___y_5210_,
                        );
                        crate::leanh::lean_dec_ref(v_fvars_5203_);
                        if crate::leanh::lean_obj_tag(v___x_5235_) == 0 {
                            v_a_5236_ = crate::leanh::lean_ctor_get(v___x_5235_, 0);
                            crate::leanh::lean_inc(v_a_5236_);
                            crate::leanh::lean_dec_ref_known(v___x_5235_, 1);
                            v___x_5237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5198_, v_post_5199_, v_usedLetOnly_5200_, v_skipConstInApp_5201_, v_skipInstances_5202_, v_a_5236_, v_a_5205_, v_snd_5231_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
                            return v___x_5237_;
                        } else {
                            crate::leanh::lean_dec(v_snd_5231_);
                            crate::leanh::lean_dec_ref(v_post_5199_);
                            crate::leanh::lean_dec_ref(v_pre_5198_);
                            v_a_5238_ = crate::leanh::lean_ctor_get(v___x_5235_, 0);
                            v_isSharedCheck_5245_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5235_)) as u8;
                            if v_isSharedCheck_5245_ == 0 {
                                v___x_5240_ = v___x_5235_;
                                v_isShared_5241_ = v_isSharedCheck_5245_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5238_);
                                crate::leanh::lean_dec(v___x_5235_);
                                v___x_5240_ = crate::leanh::lean_box(0);
                                v_isShared_5241_ = v_isSharedCheck_5245_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fvars_5203_);
                        crate::leanh::lean_dec_ref(v_post_5199_);
                        crate::leanh::lean_dec_ref(v_pre_5198_);
                        return v___x_5228_;
                    }
                }
            }
            1 => {
                if v_isShared_5241_ == 0 {
                    v___x_5243_ = v___x_5240_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
                    v___x_5243_ = v_reuseFailAlloc_5244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(
    mut v_fvars_5246_: *mut crate::leanh::LeanObject,
    mut v_pre_5247_: *mut crate::leanh::LeanObject,
    mut v_post_5248_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5249_: u8,
    mut v_skipConstInApp_5250_: u8,
    mut v_skipInstances_5251_: u8,
    mut v_body_5252_: *mut crate::leanh::LeanObject,
    mut v_x_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
    mut v___y_5256_: *mut crate::leanh::LeanObject,
    mut v___y_5257_: *mut crate::leanh::LeanObject,
    mut v___y_5258_: *mut crate::leanh::LeanObject,
    mut v___y_5259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5261_ = lean_array_push(v_fvars_5246_, v_x_5253_);
    v___x_5262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_5247_, v_post_5248_, v_usedLetOnly_5249_, v_skipConstInApp_5250_, v_skipInstances_5251_, v___x_5261_, v_body_5252_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
    return v___x_5262_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed(
    mut v_fvars_5263_: *mut crate::leanh::LeanObject,
    mut v_pre_5264_: *mut crate::leanh::LeanObject,
    mut v_post_5265_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5266_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5267_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5268_: *mut crate::leanh::LeanObject,
    mut v_body_5269_: *mut crate::leanh::LeanObject,
    mut v_x_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
    mut v___y_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5278_: u8 = 0;
    let mut v_skipConstInApp_boxed_5279_: u8 = 0;
    let mut v_skipInstances_boxed_5280_: u8 = 0;
    let mut v_res_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5278_ = (crate::leanh::lean_unbox(v_usedLetOnly_5266_) as u8);
    v_skipConstInApp_boxed_5279_ = (crate::leanh::lean_unbox(v_skipConstInApp_5267_) as u8);
    v_skipInstances_boxed_5280_ = (crate::leanh::lean_unbox(v_skipInstances_5268_) as u8);
    v_res_5281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0(v_fvars_5263_, v_pre_5264_, v_post_5265_, v_usedLetOnly_boxed_5278_, v_skipConstInApp_boxed_5279_, v_skipInstances_boxed_5280_, v_body_5269_, v_x_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
    crate::leanh::lean_dec(v___y_5276_);
    crate::leanh::lean_dec_ref(v___y_5275_);
    crate::leanh::lean_dec(v___y_5274_);
    crate::leanh::lean_dec_ref(v___y_5273_);
    crate::leanh::lean_dec(v___y_5271_);
    return v_res_5281_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(
    mut v_pre_5282_: *mut crate::leanh::LeanObject,
    mut v_post_5283_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5284_: u8,
    mut v_skipConstInApp_5285_: u8,
    mut v_skipInstances_5286_: u8,
    mut v_fvars_5287_: *mut crate::leanh::LeanObject,
    mut v_e_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v___y_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_5300_: u8 = 0;
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: u8 = 0;
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5330_: u8 = 0;
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_5288_) == 8 {
                    v_declName_5296_ = crate::leanh::lean_ctor_get(v_e_5288_, 0);
                    crate::leanh::lean_inc(v_declName_5296_);
                    v_type_5297_ = crate::leanh::lean_ctor_get(v_e_5288_, 1);
                    crate::leanh::lean_inc_ref(v_type_5297_);
                    v_value_5298_ = crate::leanh::lean_ctor_get(v_e_5288_, 2);
                    crate::leanh::lean_inc_ref(v_value_5298_);
                    v_body_5299_ = crate::leanh::lean_ctor_get(v_e_5288_, 3);
                    crate::leanh::lean_inc_ref(v_body_5299_);
                    v_nondep_5300_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_5288_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_5288_, 4);
                    v___x_5301_ = lean_expr_instantiate_rev(v_type_5297_, v_fvars_5287_);
                    crate::leanh::lean_dec_ref(v_type_5297_);
                    crate::leanh::lean_inc_ref(v_post_5283_);
                    crate::leanh::lean_inc_ref(v_pre_5282_);
                    v___x_5302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5282_, v_post_5283_, v_usedLetOnly_5284_, v_skipConstInApp_5285_, v_skipInstances_5286_, v___x_5301_, v_a_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
                    if crate::leanh::lean_obj_tag(v___x_5302_) == 0 {
                        v_a_5303_ = crate::leanh::lean_ctor_get(v___x_5302_, 0);
                        crate::leanh::lean_inc(v_a_5303_);
                        crate::leanh::lean_dec_ref_known(v___x_5302_, 1);
                        v_fst_5304_ = crate::leanh::lean_ctor_get(v_a_5303_, 0);
                        crate::leanh::lean_inc(v_fst_5304_);
                        v_snd_5305_ = crate::leanh::lean_ctor_get(v_a_5303_, 1);
                        crate::leanh::lean_inc(v_snd_5305_);
                        crate::leanh::lean_dec(v_a_5303_);
                        v___x_5306_ = lean_expr_instantiate_rev(v_value_5298_, v_fvars_5287_);
                        crate::leanh::lean_dec_ref(v_value_5298_);
                        crate::leanh::lean_inc_ref(v_post_5283_);
                        crate::leanh::lean_inc_ref(v_pre_5282_);
                        v___x_5307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5282_, v_post_5283_, v_usedLetOnly_5284_, v_skipConstInApp_5285_, v_skipInstances_5286_, v___x_5306_, v_a_5289_, v_snd_5305_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
                        if crate::leanh::lean_obj_tag(v___x_5307_) == 0 {
                            v_a_5308_ = crate::leanh::lean_ctor_get(v___x_5307_, 0);
                            crate::leanh::lean_inc(v_a_5308_);
                            crate::leanh::lean_dec_ref_known(v___x_5307_, 1);
                            v_fst_5309_ = crate::leanh::lean_ctor_get(v_a_5308_, 0);
                            crate::leanh::lean_inc(v_fst_5309_);
                            v_snd_5310_ = crate::leanh::lean_ctor_get(v_a_5308_, 1);
                            crate::leanh::lean_inc(v_snd_5310_);
                            crate::leanh::lean_dec(v_a_5308_);
                            v___x_5311_ = crate::leanh::lean_box((v_usedLetOnly_5284_) as usize);
                            v___x_5312_ = crate::leanh::lean_box((v_skipConstInApp_5285_) as usize);
                            v___x_5313_ = crate::leanh::lean_box((v_skipInstances_5286_) as usize);
                            v___f_5314_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
                            crate::leanh::lean_closure_set(v___f_5314_, 0, v_fvars_5287_);
                            crate::leanh::lean_closure_set(v___f_5314_, 1, v_pre_5282_);
                            crate::leanh::lean_closure_set(v___f_5314_, 2, v_post_5283_);
                            crate::leanh::lean_closure_set(v___f_5314_, 3, v___x_5311_);
                            crate::leanh::lean_closure_set(v___f_5314_, 4, v___x_5312_);
                            crate::leanh::lean_closure_set(v___f_5314_, 5, v___x_5313_);
                            crate::leanh::lean_closure_set(v___f_5314_, 6, v_body_5299_);
                            v___x_5315_ = 0;
                            v___x_5316_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_declName_5296_, v_fst_5304_, v_fst_5309_, v___f_5314_, v_nondep_5300_, v___x_5315_, v_a_5289_, v_snd_5310_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
                            return v___x_5316_;
                        } else {
                            crate::leanh::lean_dec(v_fst_5304_);
                            crate::leanh::lean_dec_ref(v_body_5299_);
                            crate::leanh::lean_dec(v_declName_5296_);
                            crate::leanh::lean_dec_ref(v_fvars_5287_);
                            crate::leanh::lean_dec_ref(v_post_5283_);
                            crate::leanh::lean_dec_ref(v_pre_5282_);
                            return v___x_5307_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5299_);
                        crate::leanh::lean_dec_ref(v_value_5298_);
                        crate::leanh::lean_dec(v_declName_5296_);
                        crate::leanh::lean_dec_ref(v_fvars_5287_);
                        crate::leanh::lean_dec_ref(v_post_5283_);
                        crate::leanh::lean_dec_ref(v_pre_5282_);
                        return v___x_5302_;
                    }
                } else {
                    v___x_5317_ = lean_expr_instantiate_rev(v_e_5288_, v_fvars_5287_);
                    crate::leanh::lean_dec_ref(v_e_5288_);
                    crate::leanh::lean_inc_ref(v_post_5283_);
                    crate::leanh::lean_inc_ref(v_pre_5282_);
                    v___x_5318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5282_, v_post_5283_, v_usedLetOnly_5284_, v_skipConstInApp_5285_, v_skipInstances_5286_, v___x_5317_, v_a_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
                    if crate::leanh::lean_obj_tag(v___x_5318_) == 0 {
                        v_a_5319_ = crate::leanh::lean_ctor_get(v___x_5318_, 0);
                        crate::leanh::lean_inc(v_a_5319_);
                        crate::leanh::lean_dec_ref_known(v___x_5318_, 1);
                        v_fst_5320_ = crate::leanh::lean_ctor_get(v_a_5319_, 0);
                        crate::leanh::lean_inc(v_fst_5320_);
                        v_snd_5321_ = crate::leanh::lean_ctor_get(v_a_5319_, 1);
                        crate::leanh::lean_inc(v_snd_5321_);
                        crate::leanh::lean_dec(v_a_5319_);
                        v___x_5322_ = 0;
                        v___x_5323_ = 1;
                        v___x_5324_ = l_Lean_Meta_mkLetFVars(
                            v_fvars_5287_,
                            v_fst_5320_,
                            v_usedLetOnly_5284_,
                            v___x_5322_,
                            v___x_5323_,
                            v___y_5291_,
                            v___y_5292_,
                            v___y_5293_,
                            v___y_5294_,
                        );
                        crate::leanh::lean_dec_ref(v_fvars_5287_);
                        if crate::leanh::lean_obj_tag(v___x_5324_) == 0 {
                            v_a_5325_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                            crate::leanh::lean_inc(v_a_5325_);
                            crate::leanh::lean_dec_ref_known(v___x_5324_, 1);
                            v___x_5326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5282_, v_post_5283_, v_usedLetOnly_5284_, v_skipConstInApp_5285_, v_skipInstances_5286_, v_a_5325_, v_a_5289_, v_snd_5321_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
                            return v___x_5326_;
                        } else {
                            crate::leanh::lean_dec(v_snd_5321_);
                            crate::leanh::lean_dec_ref(v_post_5283_);
                            crate::leanh::lean_dec_ref(v_pre_5282_);
                            v_a_5327_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                            v_isSharedCheck_5334_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5324_)) as u8;
                            if v_isSharedCheck_5334_ == 0 {
                                v___x_5329_ = v___x_5324_;
                                v_isShared_5330_ = v_isSharedCheck_5334_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5327_);
                                crate::leanh::lean_dec(v___x_5324_);
                                v___x_5329_ = crate::leanh::lean_box(0);
                                v_isShared_5330_ = v_isSharedCheck_5334_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fvars_5287_);
                        crate::leanh::lean_dec_ref(v_post_5283_);
                        crate::leanh::lean_dec_ref(v_pre_5282_);
                        return v___x_5318_;
                    }
                }
            }
            1 => {
                if v_isShared_5330_ == 0 {
                    v___x_5332_ = v___x_5329_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
                    v___x_5332_ = v_reuseFailAlloc_5333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(
    mut v_pre_5335_: *mut crate::leanh::LeanObject,
    mut v_post_5336_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5337_: u8,
    mut v_skipConstInApp_5338_: u8,
    mut v_skipInstances_5339_: u8,
    mut v_sz_5340_: usize,
    mut v_i_5341_: usize,
    mut v_bs_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5350_: u8 = 0;
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5367_: u8 = 0;
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5350_ = lean_usize_dec_lt(v_i_5341_, v_sz_5340_);
                if v___x_5350_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_5336_);
                    crate::leanh::lean_dec_ref(v_pre_5335_);
                    v___x_5351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5351_, 0, v_bs_5342_);
                    crate::leanh::lean_ctor_set(v___x_5351_, 1, v___y_5344_);
                    v___x_5352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5352_, 0, v___x_5351_);
                    return v___x_5352_;
                } else {
                    v_v_5353_ = lean_array_uget_borrowed(v_bs_5342_, v_i_5341_);
                    crate::leanh::lean_inc(v_v_5353_);
                    crate::leanh::lean_inc_ref(v_post_5336_);
                    crate::leanh::lean_inc_ref(v_pre_5335_);
                    v___x_5354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5335_, v_post_5336_, v_usedLetOnly_5337_, v_skipConstInApp_5338_, v_skipInstances_5339_, v_v_5353_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
                    if crate::leanh::lean_obj_tag(v___x_5354_) == 0 {
                        v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5354_, 0);
                        crate::leanh::lean_inc(v_a_5355_);
                        crate::leanh::lean_dec_ref_known(v___x_5354_, 1);
                        v_fst_5356_ = crate::leanh::lean_ctor_get(v_a_5355_, 0);
                        crate::leanh::lean_inc(v_fst_5356_);
                        v_snd_5357_ = crate::leanh::lean_ctor_get(v_a_5355_, 1);
                        crate::leanh::lean_inc(v_snd_5357_);
                        crate::leanh::lean_dec(v_a_5355_);
                        v___x_5358_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5359_ = lean_array_uset(v_bs_5342_, v_i_5341_, v___x_5358_);
                        v___x_5360_ = 1usize;
                        v___x_5361_ = lean_usize_add(v_i_5341_, v___x_5360_);
                        v___x_5362_ = lean_array_uset(v_bs_x27_5359_, v_i_5341_, v_fst_5356_);
                        v_i_5341_ = v___x_5361_;
                        v_bs_5342_ = v___x_5362_;
                        v___y_5344_ = v_snd_5357_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5342_);
                        crate::leanh::lean_dec_ref(v_post_5336_);
                        crate::leanh::lean_dec_ref(v_pre_5335_);
                        v_a_5364_ = crate::leanh::lean_ctor_get(v___x_5354_, 0);
                        v_isSharedCheck_5371_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5354_)) as u8;
                        if v_isSharedCheck_5371_ == 0 {
                            v___x_5366_ = v___x_5354_;
                            v_isShared_5367_ = v_isSharedCheck_5371_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5364_);
                            crate::leanh::lean_dec(v___x_5354_);
                            v___x_5366_ = crate::leanh::lean_box(0);
                            v_isShared_5367_ = v_isSharedCheck_5371_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5367_ == 0 {
                    v___x_5369_ = v___x_5366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5364_);
                    v___x_5369_ = v_reuseFailAlloc_5370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(
    mut v_pre_5372_: *mut crate::leanh::LeanObject,
    mut v_post_5373_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5374_: u8,
    mut v_skipConstInApp_5375_: u8,
    mut v_skipInstances_5376_: u8,
    mut v___x_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v_b_5379_: *mut crate::leanh::LeanObject,
    mut v_a_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v_fst_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5405_: u8 = 0;
    let mut v_isSharedCheck_5406_: u8 = 0;
    let mut v_a_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5410_: u8 = 0;
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5372_, v_post_5373_, v_usedLetOnly_5374_, v_skipConstInApp_5375_, v_skipInstances_5376_, v___x_5377_, v___y_5378_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
                if crate::leanh::lean_obj_tag(v___x_5387_) == 0 {
                    v_a_5388_ = crate::leanh::lean_ctor_get(v___x_5387_, 0);
                    v_isSharedCheck_5406_ = (!crate::leanh::lean_is_exclusive(v___x_5387_)) as u8;
                    if v_isSharedCheck_5406_ == 0 {
                        v___x_5390_ = v___x_5387_;
                        v_isShared_5391_ = v_isSharedCheck_5406_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5388_);
                        crate::leanh::lean_dec(v___x_5387_);
                        v___x_5390_ = crate::leanh::lean_box(0);
                        v_isShared_5391_ = v_isSharedCheck_5406_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_5379_);
                    v_a_5407_ = crate::leanh::lean_ctor_get(v___x_5387_, 0);
                    v_isSharedCheck_5414_ = (!crate::leanh::lean_is_exclusive(v___x_5387_)) as u8;
                    if v_isSharedCheck_5414_ == 0 {
                        v___x_5409_ = v___x_5387_;
                        v_isShared_5410_ = v_isSharedCheck_5414_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5407_);
                        crate::leanh::lean_dec(v___x_5387_);
                        v___x_5409_ = crate::leanh::lean_box(0);
                        v_isShared_5410_ = v_isSharedCheck_5414_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5392_ = crate::leanh::lean_ctor_get(v_a_5388_, 0);
                v_snd_5393_ = crate::leanh::lean_ctor_get(v_a_5388_, 1);
                v_isSharedCheck_5405_ = (!crate::leanh::lean_is_exclusive(v_a_5388_)) as u8;
                if v_isSharedCheck_5405_ == 0 {
                    v___x_5395_ = v_a_5388_;
                    v_isShared_5396_ = v_isSharedCheck_5405_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5393_);
                    crate::leanh::lean_inc(v_fst_5392_);
                    crate::leanh::lean_dec(v_a_5388_);
                    v___x_5395_ = crate::leanh::lean_box(0);
                    v_isShared_5396_ = v_isSharedCheck_5405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5397_ = lean_array_fset(v_b_5379_, v_a_5380_, v_fst_5392_);
                v___x_5398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5398_, 0, v___x_5397_);
                if v_isShared_5396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5395_, 0, v___x_5398_);
                    v___x_5400_ = v___x_5395_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5404_, 0, v___x_5398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5404_, 1, v_snd_5393_);
                    v___x_5400_ = v_reuseFailAlloc_5404_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5390_, 0, v___x_5400_);
                    v___x_5402_ = v___x_5390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5403_, 0, v___x_5400_);
                    v___x_5402_ = v_reuseFailAlloc_5403_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5402_;
            }
            5 => {
                if v_isShared_5410_ == 0 {
                    v___x_5412_ = v___x_5409_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
                    v___x_5412_ = v_reuseFailAlloc_5413_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed(
    mut v_pre_5415_: *mut crate::leanh::LeanObject,
    mut v_post_5416_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5417_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5418_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5419_: *mut crate::leanh::LeanObject,
    mut v___x_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v_b_5422_: *mut crate::leanh::LeanObject,
    mut v_a_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5430_: u8 = 0;
    let mut v_skipConstInApp_boxed_5431_: u8 = 0;
    let mut v_skipInstances_boxed_5432_: u8 = 0;
    let mut v_res_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5430_ = (crate::leanh::lean_unbox(v_usedLetOnly_5417_) as u8);
    v_skipConstInApp_boxed_5431_ = (crate::leanh::lean_unbox(v_skipConstInApp_5418_) as u8);
    v_skipInstances_boxed_5432_ = (crate::leanh::lean_unbox(v_skipInstances_5419_) as u8);
    v_res_5433_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0(v_pre_5415_, v_post_5416_, v_usedLetOnly_boxed_5430_, v_skipConstInApp_boxed_5431_, v_skipInstances_boxed_5432_, v___x_5420_, v___y_5421_, v_b_5422_, v_a_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_);
    crate::leanh::lean_dec(v___y_5428_);
    crate::leanh::lean_dec_ref(v___y_5427_);
    crate::leanh::lean_dec(v___y_5426_);
    crate::leanh::lean_dec_ref(v___y_5425_);
    crate::leanh::lean_dec(v_a_5423_);
    crate::leanh::lean_dec(v___y_5421_);
    return v_res_5433_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(
    mut v_upperBound_5434_: *mut crate::leanh::LeanObject,
    mut v___x_5435_: *mut crate::leanh::LeanObject,
    mut v_pre_5436_: *mut crate::leanh::LeanObject,
    mut v_post_5437_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5438_: u8,
    mut v_skipConstInApp_5439_: u8,
    mut v_skipInstances_5440_: u8,
    mut v_a_5441_: *mut crate::leanh::LeanObject,
    mut v_b_5442_: *mut crate::leanh::LeanObject,
    mut v___y_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
    mut v___y_5447_: *mut crate::leanh::LeanObject,
    mut v___y_5448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v_fst_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v_a_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v_unused_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_a_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5480_: u8 = 0;
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5484_: u8 = 0;
    let mut v___x_5485_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: u8 = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_5496_: u8 = 0;
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5485_ = lean_nat_dec_lt(v_a_5441_, v_upperBound_5434_);
                if v___x_5485_ == 0 {
                    crate::leanh::lean_dec(v_a_5441_);
                    crate::leanh::lean_dec_ref(v_post_5437_);
                    crate::leanh::lean_dec_ref(v_pre_5436_);
                    v___x_5486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5486_, 0, v_b_5442_);
                    crate::leanh::lean_ctor_set(v___x_5486_, 1, v___y_5444_);
                    v___x_5487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5487_, 0, v___x_5486_);
                    return v___x_5487_;
                } else {
                    v___x_5488_ = lean_array_fget_borrowed(v_b_5442_, v_a_5441_);
                    v___x_5489_ = lean_array_get_size(v___x_5435_);
                    v___x_5490_ = lean_nat_dec_lt(v_a_5441_, v___x_5489_);
                    if v___x_5490_ == 0 {
                        crate::leanh::lean_inc(v___x_5488_);
                        v___x_5491_ = crate::leanh::lean_box((v_usedLetOnly_5438_) as usize);
                        v___x_5492_ = crate::leanh::lean_box((v_skipConstInApp_5439_) as usize);
                        v___x_5493_ = crate::leanh::lean_box((v_skipInstances_5440_) as usize);
                        crate::leanh::lean_inc(v_a_5441_);
                        crate::leanh::lean_inc(v___y_5443_);
                        crate::leanh::lean_inc_ref(v_post_5437_);
                        crate::leanh::lean_inc_ref(v_pre_5436_);
                        v___f_5494_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                        crate::leanh::lean_closure_set(v___f_5494_, 0, v_pre_5436_);
                        crate::leanh::lean_closure_set(v___f_5494_, 1, v_post_5437_);
                        crate::leanh::lean_closure_set(v___f_5494_, 2, v___x_5491_);
                        crate::leanh::lean_closure_set(v___f_5494_, 3, v___x_5492_);
                        crate::leanh::lean_closure_set(v___f_5494_, 4, v___x_5493_);
                        crate::leanh::lean_closure_set(v___f_5494_, 5, v___x_5488_);
                        crate::leanh::lean_closure_set(v___f_5494_, 6, v___y_5443_);
                        crate::leanh::lean_closure_set(v___f_5494_, 7, v_b_5442_);
                        crate::leanh::lean_closure_set(v___f_5494_, 8, v_a_5441_);
                        v___y_5451_ = v___f_5494_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5495_ = lean_array_fget_borrowed(v___x_5435_, v_a_5441_);
                        v_isInstance_5496_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_5495_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_5496_ == 0 {
                            crate::leanh::lean_inc(v___x_5488_);
                            v___x_5497_ = crate::leanh::lean_box((v_usedLetOnly_5438_) as usize);
                            v___x_5498_ = crate::leanh::lean_box((v_skipConstInApp_5439_) as usize);
                            v___x_5499_ = crate::leanh::lean_box((v_skipInstances_5440_) as usize);
                            crate::leanh::lean_inc(v_a_5441_);
                            crate::leanh::lean_inc(v___y_5443_);
                            crate::leanh::lean_inc_ref(v_post_5437_);
                            crate::leanh::lean_inc_ref(v_pre_5436_);
                            v___f_5500_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 9);
                            crate::leanh::lean_closure_set(v___f_5500_, 0, v_pre_5436_);
                            crate::leanh::lean_closure_set(v___f_5500_, 1, v_post_5437_);
                            crate::leanh::lean_closure_set(v___f_5500_, 2, v___x_5497_);
                            crate::leanh::lean_closure_set(v___f_5500_, 3, v___x_5498_);
                            crate::leanh::lean_closure_set(v___f_5500_, 4, v___x_5499_);
                            crate::leanh::lean_closure_set(v___f_5500_, 5, v___x_5488_);
                            crate::leanh::lean_closure_set(v___f_5500_, 6, v___y_5443_);
                            crate::leanh::lean_closure_set(v___f_5500_, 7, v_b_5442_);
                            crate::leanh::lean_closure_set(v___f_5500_, 8, v_a_5441_);
                            v___y_5451_ = v___f_5500_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5501_, 0, v_b_5442_);
                            v___f_5502_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___lam__2___boxed as *mut core::ffi::c_void, 7, 1);
                            crate::leanh::lean_closure_set(v___f_5502_, 0, v___x_5501_);
                            v___y_5451_ = v___f_5502_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5448_);
                crate::leanh::lean_inc_ref(v___y_5447_);
                crate::leanh::lean_inc(v___y_5446_);
                crate::leanh::lean_inc_ref(v___y_5445_);
                v___x_5452_ = crate::leanh::lean_apply_6(
                    v___y_5451_,
                    v___y_5444_,
                    v___y_5445_,
                    v___y_5446_,
                    v___y_5447_,
                    v___y_5448_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5452_) == 0 {
                    v_a_5453_ = crate::leanh::lean_ctor_get(v___x_5452_, 0);
                    v_isSharedCheck_5476_ = (!crate::leanh::lean_is_exclusive(v___x_5452_)) as u8;
                    if v_isSharedCheck_5476_ == 0 {
                        v___x_5455_ = v___x_5452_;
                        v_isShared_5456_ = v_isSharedCheck_5476_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5453_);
                        crate::leanh::lean_dec(v___x_5452_);
                        v___x_5455_ = crate::leanh::lean_box(0);
                        v_isShared_5456_ = v_isSharedCheck_5476_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5441_);
                    crate::leanh::lean_dec_ref(v_post_5437_);
                    crate::leanh::lean_dec_ref(v_pre_5436_);
                    v_a_5477_ = crate::leanh::lean_ctor_get(v___x_5452_, 0);
                    v_isSharedCheck_5484_ = (!crate::leanh::lean_is_exclusive(v___x_5452_)) as u8;
                    if v_isSharedCheck_5484_ == 0 {
                        v___x_5479_ = v___x_5452_;
                        v_isShared_5480_ = v_isSharedCheck_5484_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5477_);
                        crate::leanh::lean_dec(v___x_5452_);
                        v___x_5479_ = crate::leanh::lean_box(0);
                        v_isShared_5480_ = v_isSharedCheck_5484_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5457_ = crate::leanh::lean_ctor_get(v_a_5453_, 0);
                crate::leanh::lean_inc(v_fst_5457_);
                if crate::leanh::lean_obj_tag(v_fst_5457_) == 0 {
                    crate::leanh::lean_dec(v_a_5441_);
                    crate::leanh::lean_dec_ref(v_post_5437_);
                    crate::leanh::lean_dec_ref(v_pre_5436_);
                    v_snd_5458_ = crate::leanh::lean_ctor_get(v_a_5453_, 1);
                    v_isSharedCheck_5469_ = (!crate::leanh::lean_is_exclusive(v_a_5453_)) as u8;
                    if v_isSharedCheck_5469_ == 0 {
                        v_unused_5470_ = crate::leanh::lean_ctor_get(v_a_5453_, 0);
                        crate::leanh::lean_dec(v_unused_5470_);
                        v___x_5460_ = v_a_5453_;
                        v_isShared_5461_ = v_isSharedCheck_5469_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5458_);
                        crate::leanh::lean_dec(v_a_5453_);
                        v___x_5460_ = crate::leanh::lean_box(0);
                        v_isShared_5461_ = v_isSharedCheck_5469_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5455_);
                    v_snd_5471_ = crate::leanh::lean_ctor_get(v_a_5453_, 1);
                    crate::leanh::lean_inc(v_snd_5471_);
                    crate::leanh::lean_dec(v_a_5453_);
                    v_a_5472_ = crate::leanh::lean_ctor_get(v_fst_5457_, 0);
                    crate::leanh::lean_inc(v_a_5472_);
                    crate::leanh::lean_dec_ref_known(v_fst_5457_, 1);
                    v___x_5473_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5474_ = lean_nat_add(v_a_5441_, v___x_5473_);
                    crate::leanh::lean_dec(v_a_5441_);
                    v_a_5441_ = v___x_5474_;
                    v_b_5442_ = v_a_5472_;
                    v___y_5444_ = v_snd_5471_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v_a_5462_ = crate::leanh::lean_ctor_get(v_fst_5457_, 0);
                crate::leanh::lean_inc(v_a_5462_);
                crate::leanh::lean_dec_ref_known(v_fst_5457_, 1);
                if v_isShared_5461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5460_, 0, v_a_5462_);
                    v___x_5464_ = v___x_5460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_snd_5458_);
                    v___x_5464_ = v_reuseFailAlloc_5468_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5455_, 0, v___x_5464_);
                    v___x_5466_ = v___x_5455_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
                    v___x_5466_ = v_reuseFailAlloc_5467_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5466_;
            }
            6 => {
                if v_isShared_5480_ == 0 {
                    v___x_5482_ = v___x_5479_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
                    v___x_5482_ = v_reuseFailAlloc_5483_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(
    mut v_skipInstances_5503_: u8,
    mut v_pre_5504_: *mut crate::leanh::LeanObject,
    mut v_post_5505_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5506_: u8,
    mut v_skipConstInApp_5507_: u8,
    mut v_x_5508_: *mut crate::leanh::LeanObject,
    mut v_x_5509_: *mut crate::leanh::LeanObject,
    mut v_x_5510_: *mut crate::leanh::LeanObject,
    mut v___y_5511_: *mut crate::leanh::LeanObject,
    mut v___y_5512_: *mut crate::leanh::LeanObject,
    mut v___y_5513_: *mut crate::leanh::LeanObject,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5526_: usize = 0;
    let mut v___x_5527_: usize = 0;
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5537_: u8 = 0;
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5541_: u8 = 0;
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5556_: u8 = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_a_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5568_: u8 = 0;
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5508_) == 5 {
                    v_fn_5574_ = crate::leanh::lean_ctor_get(v_x_5508_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5574_);
                    v_arg_5575_ = crate::leanh::lean_ctor_get(v_x_5508_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5575_);
                    crate::leanh::lean_dec_ref_known(v_x_5508_, 2);
                    v___x_5576_ = lean_array_set(v_x_5509_, v_x_5510_, v_arg_5575_);
                    v___x_5577_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5578_ = lean_nat_sub(v_x_5510_, v___x_5577_);
                    crate::leanh::lean_dec(v_x_5510_);
                    v_x_5508_ = v_fn_5574_;
                    v_x_5509_ = v___x_5576_;
                    v_x_5510_ = v___x_5578_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_5510_);
                    if v_skipConstInApp_5507_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_5580_ = l_Lean_Expr_isConst(v_x_5508_);
                        if v___x_5580_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_5519_ = v_x_5508_;
                            v___y_5520_ = v___y_5511_;
                            v___y_5521_ = v___y_5512_;
                            v___y_5522_ = v___y_5513_;
                            v___y_5523_ = v___y_5514_;
                            v___y_5524_ = v___y_5515_;
                            v___y_5525_ = v___y_5516_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_5503_ == 0 {
                    v_sz_5526_ = lean_array_size(v_x_5509_);
                    v___x_5527_ = 0usize;
                    crate::leanh::lean_inc_ref(v_post_5505_);
                    crate::leanh::lean_inc_ref(v_pre_5504_);
                    v___x_5528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_5504_, v_post_5505_, v_usedLetOnly_5506_, v_skipConstInApp_5507_, v_skipInstances_5503_, v_sz_5526_, v___x_5527_, v_x_5509_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
                    if crate::leanh::lean_obj_tag(v___x_5528_) == 0 {
                        v_a_5529_ = crate::leanh::lean_ctor_get(v___x_5528_, 0);
                        crate::leanh::lean_inc(v_a_5529_);
                        crate::leanh::lean_dec_ref_known(v___x_5528_, 1);
                        v_fst_5530_ = crate::leanh::lean_ctor_get(v_a_5529_, 0);
                        crate::leanh::lean_inc(v_fst_5530_);
                        v_snd_5531_ = crate::leanh::lean_ctor_get(v_a_5529_, 1);
                        crate::leanh::lean_inc(v_snd_5531_);
                        crate::leanh::lean_dec(v_a_5529_);
                        v___x_5532_ = l_Lean_mkAppN(v_f_5519_, v_fst_5530_);
                        crate::leanh::lean_dec(v_fst_5530_);
                        v___x_5533_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5504_, v_post_5505_, v_usedLetOnly_5506_, v_skipConstInApp_5507_, v_skipInstances_5503_, v___x_5532_, v___y_5520_, v_snd_5531_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
                        return v___x_5533_;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_5519_);
                        crate::leanh::lean_dec_ref(v_post_5505_);
                        crate::leanh::lean_dec_ref(v_pre_5504_);
                        v_a_5534_ = crate::leanh::lean_ctor_get(v___x_5528_, 0);
                        v_isSharedCheck_5541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5528_)) as u8;
                        if v_isSharedCheck_5541_ == 0 {
                            v___x_5536_ = v___x_5528_;
                            v_isShared_5537_ = v_isSharedCheck_5541_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5534_);
                            crate::leanh::lean_dec(v___x_5528_);
                            v___x_5536_ = crate::leanh::lean_box(0);
                            v_isShared_5537_ = v_isSharedCheck_5541_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_5542_ = lean_array_get_size(v_x_5509_);
                    crate::leanh::lean_inc_ref(v_f_5519_);
                    v___x_5543_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_5519_,
                        v___x_5542_,
                        v___y_5522_,
                        v___y_5523_,
                        v___y_5524_,
                        v___y_5525_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5543_) == 0 {
                        v_a_5544_ = crate::leanh::lean_ctor_get(v___x_5543_, 0);
                        crate::leanh::lean_inc(v_a_5544_);
                        crate::leanh::lean_dec_ref_known(v___x_5543_, 1);
                        v_paramInfo_5545_ = crate::leanh::lean_ctor_get(v_a_5544_, 0);
                        crate::leanh::lean_inc_ref(v_paramInfo_5545_);
                        crate::leanh::lean_dec(v_a_5544_);
                        v___x_5546_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_post_5505_);
                        crate::leanh::lean_inc_ref(v_pre_5504_);
                        v___x_5547_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v___x_5542_, v_paramInfo_5545_, v_pre_5504_, v_post_5505_, v_usedLetOnly_5506_, v_skipConstInApp_5507_, v_skipInstances_5503_, v___x_5546_, v_x_5509_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
                        crate::leanh::lean_dec_ref(v_paramInfo_5545_);
                        if crate::leanh::lean_obj_tag(v___x_5547_) == 0 {
                            v_a_5548_ = crate::leanh::lean_ctor_get(v___x_5547_, 0);
                            crate::leanh::lean_inc(v_a_5548_);
                            crate::leanh::lean_dec_ref_known(v___x_5547_, 1);
                            v_fst_5549_ = crate::leanh::lean_ctor_get(v_a_5548_, 0);
                            crate::leanh::lean_inc(v_fst_5549_);
                            v_snd_5550_ = crate::leanh::lean_ctor_get(v_a_5548_, 1);
                            crate::leanh::lean_inc(v_snd_5550_);
                            crate::leanh::lean_dec(v_a_5548_);
                            v___x_5551_ = l_Lean_mkAppN(v_f_5519_, v_fst_5549_);
                            crate::leanh::lean_dec(v_fst_5549_);
                            v___x_5552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5504_, v_post_5505_, v_usedLetOnly_5506_, v_skipConstInApp_5507_, v_skipInstances_5503_, v___x_5551_, v___y_5520_, v_snd_5550_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
                            return v___x_5552_;
                        } else {
                            crate::leanh::lean_dec_ref(v_f_5519_);
                            crate::leanh::lean_dec_ref(v_post_5505_);
                            crate::leanh::lean_dec_ref(v_pre_5504_);
                            v_a_5553_ = crate::leanh::lean_ctor_get(v___x_5547_, 0);
                            v_isSharedCheck_5560_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5547_)) as u8;
                            if v_isSharedCheck_5560_ == 0 {
                                v___x_5555_ = v___x_5547_;
                                v_isShared_5556_ = v_isSharedCheck_5560_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5553_);
                                crate::leanh::lean_dec(v___x_5547_);
                                v___x_5555_ = crate::leanh::lean_box(0);
                                v_isShared_5556_ = v_isSharedCheck_5560_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_5521_);
                        crate::leanh::lean_dec_ref(v_f_5519_);
                        crate::leanh::lean_dec_ref(v_x_5509_);
                        crate::leanh::lean_dec_ref(v_post_5505_);
                        crate::leanh::lean_dec_ref(v_pre_5504_);
                        v_a_5561_ = crate::leanh::lean_ctor_get(v___x_5543_, 0);
                        v_isSharedCheck_5568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5543_)) as u8;
                        if v_isSharedCheck_5568_ == 0 {
                            v___x_5563_ = v___x_5543_;
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5561_);
                            crate::leanh::lean_dec(v___x_5543_);
                            v___x_5563_ = crate::leanh::lean_box(0);
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5537_ == 0 {
                    v___x_5539_ = v___x_5536_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5534_);
                    v___x_5539_ = v_reuseFailAlloc_5540_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5539_;
            }
            4 => {
                if v_isShared_5556_ == 0 {
                    v___x_5558_ = v___x_5555_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_a_5553_);
                    v___x_5558_ = v_reuseFailAlloc_5559_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5558_;
            }
            6 => {
                if v_isShared_5564_ == 0 {
                    v___x_5566_ = v___x_5563_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
                    v___x_5566_ = v_reuseFailAlloc_5567_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5566_;
            }
            8 => {
                crate::leanh::lean_inc_ref(v_post_5505_);
                crate::leanh::lean_inc_ref(v_pre_5504_);
                v___x_5570_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5504_, v_post_5505_, v_usedLetOnly_5506_, v_skipConstInApp_5507_, v_skipInstances_5503_, v_x_5508_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
                if crate::leanh::lean_obj_tag(v___x_5570_) == 0 {
                    v_a_5571_ = crate::leanh::lean_ctor_get(v___x_5570_, 0);
                    crate::leanh::lean_inc(v_a_5571_);
                    crate::leanh::lean_dec_ref_known(v___x_5570_, 1);
                    v_fst_5572_ = crate::leanh::lean_ctor_get(v_a_5571_, 0);
                    crate::leanh::lean_inc(v_fst_5572_);
                    v_snd_5573_ = crate::leanh::lean_ctor_get(v_a_5571_, 1);
                    crate::leanh::lean_inc(v_snd_5573_);
                    crate::leanh::lean_dec(v_a_5571_);
                    v_f_5519_ = v_fst_5572_;
                    v___y_5520_ = v___y_5511_;
                    v___y_5521_ = v_snd_5573_;
                    v___y_5522_ = v___y_5513_;
                    v___y_5523_ = v___y_5514_;
                    v___y_5524_ = v___y_5515_;
                    v___y_5525_ = v___y_5516_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_x_5509_);
                    crate::leanh::lean_dec_ref(v_post_5505_);
                    crate::leanh::lean_dec_ref(v_pre_5504_);
                    return v___x_5570_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(
    mut v___x_5581_: *mut crate::leanh::LeanObject,
    mut v_pre_5582_: *mut crate::leanh::LeanObject,
    mut v_e_5583_: *mut crate::leanh::LeanObject,
    mut v_post_5584_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5585_: u8,
    mut v_skipConstInApp_5586_: u8,
    mut v_skipInstances_5587_: u8,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v_fst_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___y_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: usize = 0;
    let mut v___x_5627_: usize = 0;
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: usize = 0;
    let mut v___x_5640_: usize = 0;
    let mut v___x_5641_: u8 = 0;
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut v_a_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5662_: u8 = 0;
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5666_: u8 = 0;
    let mut v_a_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5670_: u8 = 0;
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5595_ = l_Lean_Core_checkSystem(v___x_5581_, v___y_5592_, v___y_5593_);
                if crate::leanh::lean_obj_tag(v___x_5595_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5595_, 1);
                    crate::leanh::lean_inc_ref(v_pre_5582_);
                    crate::leanh::lean_inc(v___y_5593_);
                    crate::leanh::lean_inc_ref(v___y_5592_);
                    crate::leanh::lean_inc(v___y_5591_);
                    crate::leanh::lean_inc_ref(v___y_5590_);
                    crate::leanh::lean_inc_ref(v_e_5583_);
                    v___x_5596_ = crate::leanh::lean_apply_7(
                        v_pre_5582_,
                        v_e_5583_,
                        v___y_5589_,
                        v___y_5590_,
                        v___y_5591_,
                        v___y_5592_,
                        v___y_5593_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5596_) == 0 {
                        v_a_5597_ = crate::leanh::lean_ctor_get(v___x_5596_, 0);
                        v_isSharedCheck_5658_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5596_)) as u8;
                        if v_isSharedCheck_5658_ == 0 {
                            v___x_5599_ = v___x_5596_;
                            v_isShared_5600_ = v_isSharedCheck_5658_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5597_);
                            crate::leanh::lean_dec(v___x_5596_);
                            v___x_5599_ = crate::leanh::lean_box(0);
                            v_isShared_5600_ = v_isSharedCheck_5658_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_5584_);
                        crate::leanh::lean_dec_ref(v_e_5583_);
                        crate::leanh::lean_dec_ref(v_pre_5582_);
                        v_a_5659_ = crate::leanh::lean_ctor_get(v___x_5596_, 0);
                        v_isSharedCheck_5666_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5596_)) as u8;
                        if v_isSharedCheck_5666_ == 0 {
                            v___x_5661_ = v___x_5596_;
                            v_isShared_5662_ = v_isSharedCheck_5666_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5659_);
                            crate::leanh::lean_dec(v___x_5596_);
                            v___x_5661_ = crate::leanh::lean_box(0);
                            v_isShared_5662_ = v_isSharedCheck_5666_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5589_);
                    crate::leanh::lean_dec_ref(v_post_5584_);
                    crate::leanh::lean_dec_ref(v_e_5583_);
                    crate::leanh::lean_dec_ref(v_pre_5582_);
                    v_a_5667_ = crate::leanh::lean_ctor_get(v___x_5595_, 0);
                    v_isSharedCheck_5674_ = (!crate::leanh::lean_is_exclusive(v___x_5595_)) as u8;
                    if v_isSharedCheck_5674_ == 0 {
                        v___x_5669_ = v___x_5595_;
                        v_isShared_5670_ = v_isSharedCheck_5674_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5667_);
                        crate::leanh::lean_dec(v___x_5595_);
                        v___x_5669_ = crate::leanh::lean_box(0);
                        v_isShared_5670_ = v_isSharedCheck_5674_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5601_ = crate::leanh::lean_ctor_get(v_a_5597_, 0);
                v_snd_5602_ = crate::leanh::lean_ctor_get(v_a_5597_, 1);
                v_isSharedCheck_5657_ = (!crate::leanh::lean_is_exclusive(v_a_5597_)) as u8;
                if v_isSharedCheck_5657_ == 0 {
                    v___x_5604_ = v_a_5597_;
                    v_isShared_5605_ = v_isSharedCheck_5657_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5602_);
                    crate::leanh::lean_inc(v_fst_5601_);
                    crate::leanh::lean_dec(v_a_5597_);
                    v___x_5604_ = crate::leanh::lean_box(0);
                    v_isShared_5605_ = v_isSharedCheck_5657_;
                    state = 2;
                    continue;
                }
            }
            2 => match crate::leanh::lean_obj_tag(v_fst_5601_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_5584_);
                    crate::leanh::lean_dec_ref(v_e_5583_);
                    crate::leanh::lean_dec_ref(v_pre_5582_);
                    v_e_5646_ = crate::leanh::lean_ctor_get(v_fst_5601_, 0);
                    crate::leanh::lean_inc_ref(v_e_5646_);
                    crate::leanh::lean_dec_ref_known(v_fst_5601_, 1);
                    if v_isShared_5605_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5604_, 0, v_e_5646_);
                        v___x_5648_ = v___x_5604_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_e_5646_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_snd_5602_);
                        v___x_5648_ = v_reuseFailAlloc_5652_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_5604_);
                    crate::leanh::lean_del_object(v___x_5599_);
                    crate::leanh::lean_dec_ref(v_e_5583_);
                    v_e_5653_ = crate::leanh::lean_ctor_get(v_fst_5601_, 0);
                    crate::leanh::lean_inc_ref(v_e_5653_);
                    crate::leanh::lean_dec_ref_known(v_fst_5601_, 1);
                    v___x_5654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v_e_5653_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                    return v___x_5654_;
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_5604_);
                    crate::leanh::lean_del_object(v___x_5599_);
                    v_e_x3f_5655_ = crate::leanh::lean_ctor_get(v_fst_5601_, 0);
                    crate::leanh::lean_inc(v_e_x3f_5655_);
                    crate::leanh::lean_dec_ref_known(v_fst_5601_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_5655_) == 0 {
                        v___y_5607_ = v_e_5583_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5583_);
                        v_val_5656_ = crate::leanh::lean_ctor_get(v_e_x3f_5655_, 0);
                        crate::leanh::lean_inc(v_val_5656_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_5655_, 1);
                        v___y_5607_ = v_val_5656_;
                        state = 3;
                        continue;
                    }
                }
            },
            3 => {
                match crate::leanh::lean_obj_tag(v___y_5607_) {
                    7 => {
                        v___x_5608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0;
                        v___x_5609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___x_5608_, v___y_5607_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        return v___x_5609_;
                    }
                    6 => {
                        v___x_5610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0;
                        v___x_5611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___x_5610_, v___y_5607_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        return v___x_5611_;
                    }
                    8 => {
                        v___x_5612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___closed__0;
                        v___x_5613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___x_5612_, v___y_5607_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        return v___x_5613_;
                    }
                    5 => {
                        v_dummy_5614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0_once), _init_l___private_Lean_Meta_Coe_0__Lean_Meta_recProjTarget___closed__0);
                        v_nargs_5615_ = l_Lean_Expr_getAppNumArgs(v___y_5607_);
                        crate::leanh::lean_inc(v_nargs_5615_);
                        v___x_5616_ = lean_mk_array(v_nargs_5615_, v_dummy_5614_);
                        v___x_5617_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5618_ = lean_nat_sub(v_nargs_5615_, v___x_5617_);
                        crate::leanh::lean_dec(v_nargs_5615_);
                        v___x_5619_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_5587_, v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v___y_5607_, v___x_5616_, v___x_5618_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        return v___x_5619_;
                    }
                    10 => {
                        v_data_5620_ = crate::leanh::lean_ctor_get(v___y_5607_, 0);
                        v_expr_5621_ = crate::leanh::lean_ctor_get(v___y_5607_, 1);
                        crate::leanh::lean_inc_ref(v_expr_5621_);
                        crate::leanh::lean_inc_ref(v_post_5584_);
                        crate::leanh::lean_inc_ref(v_pre_5582_);
                        v___x_5622_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v_expr_5621_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        if crate::leanh::lean_obj_tag(v___x_5622_) == 0 {
                            v_a_5623_ = crate::leanh::lean_ctor_get(v___x_5622_, 0);
                            crate::leanh::lean_inc(v_a_5623_);
                            crate::leanh::lean_dec_ref_known(v___x_5622_, 1);
                            v_fst_5624_ = crate::leanh::lean_ctor_get(v_a_5623_, 0);
                            crate::leanh::lean_inc(v_fst_5624_);
                            v_snd_5625_ = crate::leanh::lean_ctor_get(v_a_5623_, 1);
                            crate::leanh::lean_inc(v_snd_5625_);
                            crate::leanh::lean_dec(v_a_5623_);
                            v___x_5626_ = lean_ptr_addr(v_expr_5621_);
                            v___x_5627_ = lean_ptr_addr(v_fst_5624_);
                            v___x_5628_ = lean_usize_dec_eq(v___x_5626_, v___x_5627_);
                            if v___x_5628_ == 0 {
                                crate::leanh::lean_inc(v_data_5620_);
                                crate::leanh::lean_dec_ref_known(v___y_5607_, 2);
                                v___x_5629_ =
                                    l_Lean_Expr_mdata___override(v_data_5620_, v_fst_5624_);
                                v___x_5630_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___x_5629_, v___y_5588_, v_snd_5625_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                                return v___x_5630_;
                            } else {
                                crate::leanh::lean_dec(v_fst_5624_);
                                v___x_5631_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___y_5607_, v___y_5588_, v_snd_5625_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                                return v___x_5631_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___y_5607_, 2);
                            crate::leanh::lean_dec_ref(v_post_5584_);
                            crate::leanh::lean_dec_ref(v_pre_5582_);
                            return v___x_5622_;
                        }
                    }
                    11 => {
                        v_typeName_5632_ = crate::leanh::lean_ctor_get(v___y_5607_, 0);
                        v_idx_5633_ = crate::leanh::lean_ctor_get(v___y_5607_, 1);
                        v_struct_5634_ = crate::leanh::lean_ctor_get(v___y_5607_, 2);
                        crate::leanh::lean_inc_ref(v_struct_5634_);
                        crate::leanh::lean_inc_ref(v_post_5584_);
                        crate::leanh::lean_inc_ref(v_pre_5582_);
                        v___x_5635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v_struct_5634_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        if crate::leanh::lean_obj_tag(v___x_5635_) == 0 {
                            v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5635_, 0);
                            crate::leanh::lean_inc(v_a_5636_);
                            crate::leanh::lean_dec_ref_known(v___x_5635_, 1);
                            v_fst_5637_ = crate::leanh::lean_ctor_get(v_a_5636_, 0);
                            crate::leanh::lean_inc(v_fst_5637_);
                            v_snd_5638_ = crate::leanh::lean_ctor_get(v_a_5636_, 1);
                            crate::leanh::lean_inc(v_snd_5638_);
                            crate::leanh::lean_dec(v_a_5636_);
                            v___x_5639_ = lean_ptr_addr(v_struct_5634_);
                            v___x_5640_ = lean_ptr_addr(v_fst_5637_);
                            v___x_5641_ = lean_usize_dec_eq(v___x_5639_, v___x_5640_);
                            if v___x_5641_ == 0 {
                                crate::leanh::lean_inc(v_idx_5633_);
                                crate::leanh::lean_inc(v_typeName_5632_);
                                crate::leanh::lean_dec_ref_known(v___y_5607_, 3);
                                v___x_5642_ = l_Lean_Expr_proj___override(
                                    v_typeName_5632_,
                                    v_idx_5633_,
                                    v_fst_5637_,
                                );
                                v___x_5643_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___x_5642_, v___y_5588_, v_snd_5638_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                                return v___x_5643_;
                            } else {
                                crate::leanh::lean_dec(v_fst_5637_);
                                v___x_5644_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___y_5607_, v___y_5588_, v_snd_5638_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                                return v___x_5644_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___y_5607_, 3);
                            crate::leanh::lean_dec_ref(v_post_5584_);
                            crate::leanh::lean_dec_ref(v_pre_5582_);
                            return v___x_5635_;
                        }
                    }
                    _ => {
                        v___x_5645_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5582_, v_post_5584_, v_usedLetOnly_5585_, v_skipConstInApp_5586_, v_skipInstances_5587_, v___y_5607_, v___y_5588_, v_snd_5602_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
                        return v___x_5645_;
                    }
                }
            }
            4 => {
                if v_isShared_5600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5599_, 0, v___x_5648_);
                    v___x_5650_ = v___x_5599_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
                    v___x_5650_ = v_reuseFailAlloc_5651_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5650_;
            }
            6 => {
                if v_isShared_5662_ == 0 {
                    v___x_5664_ = v___x_5661_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
                    v___x_5664_ = v_reuseFailAlloc_5665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5664_;
            }
            8 => {
                if v_isShared_5670_ == 0 {
                    v___x_5672_ = v___x_5669_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_a_5667_);
                    v___x_5672_ = v_reuseFailAlloc_5673_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed(
    mut v___x_5675_: *mut crate::leanh::LeanObject,
    mut v_pre_5676_: *mut crate::leanh::LeanObject,
    mut v_e_5677_: *mut crate::leanh::LeanObject,
    mut v_post_5678_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5679_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5680_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5689_: u8 = 0;
    let mut v_skipConstInApp_boxed_5690_: u8 = 0;
    let mut v_skipInstances_boxed_5691_: u8 = 0;
    let mut v_res_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5689_ = (crate::leanh::lean_unbox(v_usedLetOnly_5679_) as u8);
    v_skipConstInApp_boxed_5690_ = (crate::leanh::lean_unbox(v_skipConstInApp_5680_) as u8);
    v_skipInstances_boxed_5691_ = (crate::leanh::lean_unbox(v_skipInstances_5681_) as u8);
    v_res_5692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1(v___x_5675_, v_pre_5676_, v_e_5677_, v_post_5678_, v_usedLetOnly_boxed_5689_, v_skipConstInApp_boxed_5690_, v_skipInstances_boxed_5691_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
    crate::leanh::lean_dec(v___y_5687_);
    crate::leanh::lean_dec_ref(v___y_5686_);
    crate::leanh::lean_dec(v___y_5685_);
    crate::leanh::lean_dec_ref(v___y_5684_);
    crate::leanh::lean_dec(v___y_5682_);
    return v_res_5692_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(
    mut v_pre_5693_: *mut crate::leanh::LeanObject,
    mut v_post_5694_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5695_: u8,
    mut v_skipConstInApp_5696_: u8,
    mut v_skipInstances_5697_: u8,
    mut v_e_5698_: *mut crate::leanh::LeanObject,
    mut v_a_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
    mut v___y_5702_: *mut crate::leanh::LeanObject,
    mut v___y_5703_: *mut crate::leanh::LeanObject,
    mut v___y_5704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5711_: u8 = 0;
    let mut v_fst_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5716_: u8 = 0;
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v_snd_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5736_: u8 = 0;
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5743_: u8 = 0;
    let mut v_unused_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5745_: u8 = 0;
    let mut v_a_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5749_: u8 = 0;
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v_val_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5761_: u8 = 0;
    let mut v_isSharedCheck_5762_: u8 = 0;
    let mut v_a_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5766_: u8 = 0;
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_5699_);
                v___x_5706_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_5706_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5706_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_5706_, 2, v_a_5699_);
                v___x_5707_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(crate::leanh::lean_box(0), v___x_5706_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
                if crate::leanh::lean_obj_tag(v___x_5707_) == 0 {
                    v_a_5708_ = crate::leanh::lean_ctor_get(v___x_5707_, 0);
                    v_isSharedCheck_5762_ = (!crate::leanh::lean_is_exclusive(v___x_5707_)) as u8;
                    if v_isSharedCheck_5762_ == 0 {
                        v___x_5710_ = v___x_5707_;
                        v_isShared_5711_ = v_isSharedCheck_5762_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5708_);
                        crate::leanh::lean_dec(v___x_5707_);
                        v___x_5710_ = crate::leanh::lean_box(0);
                        v_isShared_5711_ = v_isSharedCheck_5762_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5698_);
                    crate::leanh::lean_dec_ref(v_post_5694_);
                    crate::leanh::lean_dec_ref(v_pre_5693_);
                    v_a_5763_ = crate::leanh::lean_ctor_get(v___x_5707_, 0);
                    v_isSharedCheck_5770_ = (!crate::leanh::lean_is_exclusive(v___x_5707_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5765_ = v___x_5707_;
                        v_isShared_5766_ = v_isSharedCheck_5770_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5763_);
                        crate::leanh::lean_dec(v___x_5707_);
                        v___x_5765_ = crate::leanh::lean_box(0);
                        v_isShared_5766_ = v_isSharedCheck_5770_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5712_ = crate::leanh::lean_ctor_get(v_a_5708_, 0);
                v_snd_5713_ = crate::leanh::lean_ctor_get(v_a_5708_, 1);
                v_isSharedCheck_5761_ = (!crate::leanh::lean_is_exclusive(v_a_5708_)) as u8;
                if v_isSharedCheck_5761_ == 0 {
                    v___x_5715_ = v_a_5708_;
                    v_isShared_5716_ = v_isSharedCheck_5761_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5713_);
                    crate::leanh::lean_inc(v_fst_5712_);
                    crate::leanh::lean_dec(v_a_5708_);
                    v___x_5715_ = crate::leanh::lean_box(0);
                    v_isShared_5716_ = v_isSharedCheck_5761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_fst_5712_, v_e_5698_);
                crate::leanh::lean_dec(v_fst_5712_);
                if crate::leanh::lean_obj_tag(v___x_5717_) == 0 {
                    crate::leanh::lean_del_object(v___x_5715_);
                    crate::leanh::lean_del_object(v___x_5710_);
                    v___x_5718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___closed__0;
                    v___x_5719_ = crate::leanh::lean_box((v_usedLetOnly_5695_) as usize);
                    v___x_5720_ = crate::leanh::lean_box((v_skipConstInApp_5696_) as usize);
                    v___x_5721_ = crate::leanh::lean_box((v_skipInstances_5697_) as usize);
                    crate::leanh::lean_inc_ref(v_e_5698_);
                    v___f_5722_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__1___boxed as *mut core::ffi::c_void, 14, 7);
                    crate::leanh::lean_closure_set(v___f_5722_, 0, v___x_5718_);
                    crate::leanh::lean_closure_set(v___f_5722_, 1, v_pre_5693_);
                    crate::leanh::lean_closure_set(v___f_5722_, 2, v_e_5698_);
                    crate::leanh::lean_closure_set(v___f_5722_, 3, v_post_5694_);
                    crate::leanh::lean_closure_set(v___f_5722_, 4, v___x_5719_);
                    crate::leanh::lean_closure_set(v___f_5722_, 5, v___x_5720_);
                    crate::leanh::lean_closure_set(v___f_5722_, 6, v___x_5721_);
                    v___x_5723_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v___f_5722_, v_a_5699_, v_snd_5713_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
                    if crate::leanh::lean_obj_tag(v___x_5723_) == 0 {
                        v_a_5724_ = crate::leanh::lean_ctor_get(v___x_5723_, 0);
                        crate::leanh::lean_inc(v_a_5724_);
                        crate::leanh::lean_dec_ref_known(v___x_5723_, 1);
                        v_fst_5725_ = crate::leanh::lean_ctor_get(v_a_5724_, 0);
                        crate::leanh::lean_inc_n(v_fst_5725_, 2);
                        v_snd_5726_ = crate::leanh::lean_ctor_get(v_a_5724_, 1);
                        crate::leanh::lean_inc(v_snd_5726_);
                        crate::leanh::lean_dec(v_a_5724_);
                        crate::leanh::lean_inc(v_a_5699_);
                        v___f_5727_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_5727_, 0, v_a_5699_);
                        crate::leanh::lean_closure_set(v___f_5727_, 1, v_e_5698_);
                        crate::leanh::lean_closure_set(v___f_5727_, 2, v_fst_5725_);
                        v___x_5728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___lam__0(crate::leanh::lean_box(0), v___f_5727_, v_snd_5726_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
                        if crate::leanh::lean_obj_tag(v___x_5728_) == 0 {
                            v_a_5729_ = crate::leanh::lean_ctor_get(v___x_5728_, 0);
                            v_isSharedCheck_5745_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5728_)) as u8;
                            if v_isSharedCheck_5745_ == 0 {
                                v___x_5731_ = v___x_5728_;
                                v_isShared_5732_ = v_isSharedCheck_5745_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5729_);
                                crate::leanh::lean_dec(v___x_5728_);
                                v___x_5731_ = crate::leanh::lean_box(0);
                                v_isShared_5732_ = v_isSharedCheck_5745_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_5725_);
                            v_a_5746_ = crate::leanh::lean_ctor_get(v___x_5728_, 0);
                            v_isSharedCheck_5753_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5728_)) as u8;
                            if v_isSharedCheck_5753_ == 0 {
                                v___x_5748_ = v___x_5728_;
                                v_isShared_5749_ = v_isSharedCheck_5753_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5746_);
                                crate::leanh::lean_dec(v___x_5728_);
                                v___x_5748_ = crate::leanh::lean_box(0);
                                v_isShared_5749_ = v_isSharedCheck_5753_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5698_);
                        return v___x_5723_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5698_);
                    crate::leanh::lean_dec_ref(v_post_5694_);
                    crate::leanh::lean_dec_ref(v_pre_5693_);
                    v_val_5754_ = crate::leanh::lean_ctor_get(v___x_5717_, 0);
                    crate::leanh::lean_inc(v_val_5754_);
                    crate::leanh::lean_dec_ref_known(v___x_5717_, 1);
                    if v_isShared_5716_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5715_, 0, v_val_5754_);
                        v___x_5756_ = v___x_5715_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5760_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_val_5754_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5760_, 1, v_snd_5713_);
                        v___x_5756_ = v_reuseFailAlloc_5760_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_5733_ = crate::leanh::lean_ctor_get(v_a_5729_, 1);
                v_isSharedCheck_5743_ = (!crate::leanh::lean_is_exclusive(v_a_5729_)) as u8;
                if v_isSharedCheck_5743_ == 0 {
                    v_unused_5744_ = crate::leanh::lean_ctor_get(v_a_5729_, 0);
                    crate::leanh::lean_dec(v_unused_5744_);
                    v___x_5735_ = v_a_5729_;
                    v_isShared_5736_ = v_isSharedCheck_5743_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5733_);
                    crate::leanh::lean_dec(v_a_5729_);
                    v___x_5735_ = crate::leanh::lean_box(0);
                    v_isShared_5736_ = v_isSharedCheck_5743_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5735_, 0, v_fst_5725_);
                    v___x_5738_ = v___x_5735_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5742_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_fst_5725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5742_, 1, v_snd_5733_);
                    v___x_5738_ = v_reuseFailAlloc_5742_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5731_, 0, v___x_5738_);
                    v___x_5740_ = v___x_5731_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5738_);
                    v___x_5740_ = v_reuseFailAlloc_5741_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5740_;
            }
            7 => {
                if v_isShared_5749_ == 0 {
                    v___x_5751_ = v___x_5748_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
                    v___x_5751_ = v_reuseFailAlloc_5752_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5751_;
            }
            9 => {
                if v_isShared_5711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5710_, 0, v___x_5756_);
                    v___x_5758_ = v___x_5710_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5756_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5758_;
            }
            11 => {
                if v_isShared_5766_ == 0 {
                    v___x_5768_ = v___x_5765_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
                    v___x_5768_ = v_reuseFailAlloc_5769_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed(
    mut v_fvars_5771_: *mut crate::leanh::LeanObject,
    mut v_pre_5772_: *mut crate::leanh::LeanObject,
    mut v_post_5773_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5774_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5775_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5776_: *mut crate::leanh::LeanObject,
    mut v_body_5777_: *mut crate::leanh::LeanObject,
    mut v_x_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5786_: u8 = 0;
    let mut v_skipConstInApp_boxed_5787_: u8 = 0;
    let mut v_skipInstances_boxed_5788_: u8 = 0;
    let mut v_res_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5786_ = (crate::leanh::lean_unbox(v_usedLetOnly_5774_) as u8);
    v_skipConstInApp_boxed_5787_ = (crate::leanh::lean_unbox(v_skipConstInApp_5775_) as u8);
    v_skipInstances_boxed_5788_ = (crate::leanh::lean_unbox(v_skipInstances_5776_) as u8);
    v_res_5789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(v_fvars_5771_, v_pre_5772_, v_post_5773_, v_usedLetOnly_boxed_5786_, v_skipConstInApp_boxed_5787_, v_skipInstances_boxed_5788_, v_body_5777_, v_x_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
    crate::leanh::lean_dec(v___y_5784_);
    crate::leanh::lean_dec_ref(v___y_5783_);
    crate::leanh::lean_dec(v___y_5782_);
    crate::leanh::lean_dec_ref(v___y_5781_);
    crate::leanh::lean_dec(v___y_5779_);
    return v_res_5789_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(
    mut v_pre_5790_: *mut crate::leanh::LeanObject,
    mut v_post_5791_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5792_: u8,
    mut v_skipConstInApp_5793_: u8,
    mut v_skipInstances_5794_: u8,
    mut v_fvars_5795_: *mut crate::leanh::LeanObject,
    mut v_e_5796_: *mut crate::leanh::LeanObject,
    mut v_a_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_5807_: u8 = 0;
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: u8 = 0;
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: u8 = 0;
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5833_: u8 = 0;
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_5796_) == 7 {
                    v_binderName_5804_ = crate::leanh::lean_ctor_get(v_e_5796_, 0);
                    crate::leanh::lean_inc(v_binderName_5804_);
                    v_binderType_5805_ = crate::leanh::lean_ctor_get(v_e_5796_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5805_);
                    v_body_5806_ = crate::leanh::lean_ctor_get(v_e_5796_, 2);
                    crate::leanh::lean_inc_ref(v_body_5806_);
                    v_binderInfo_5807_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_5796_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_5796_, 3);
                    v___x_5808_ = lean_expr_instantiate_rev(v_binderType_5805_, v_fvars_5795_);
                    crate::leanh::lean_dec_ref(v_binderType_5805_);
                    crate::leanh::lean_inc_ref(v_post_5791_);
                    crate::leanh::lean_inc_ref(v_pre_5790_);
                    v___x_5809_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5790_, v_post_5791_, v_usedLetOnly_5792_, v_skipConstInApp_5793_, v_skipInstances_5794_, v___x_5808_, v_a_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
                    if crate::leanh::lean_obj_tag(v___x_5809_) == 0 {
                        v_a_5810_ = crate::leanh::lean_ctor_get(v___x_5809_, 0);
                        crate::leanh::lean_inc(v_a_5810_);
                        crate::leanh::lean_dec_ref_known(v___x_5809_, 1);
                        v_fst_5811_ = crate::leanh::lean_ctor_get(v_a_5810_, 0);
                        crate::leanh::lean_inc(v_fst_5811_);
                        v_snd_5812_ = crate::leanh::lean_ctor_get(v_a_5810_, 1);
                        crate::leanh::lean_inc(v_snd_5812_);
                        crate::leanh::lean_dec(v_a_5810_);
                        v___x_5813_ = crate::leanh::lean_box((v_usedLetOnly_5792_) as usize);
                        v___x_5814_ = crate::leanh::lean_box((v_skipConstInApp_5793_) as usize);
                        v___x_5815_ = crate::leanh::lean_box((v_skipInstances_5794_) as usize);
                        v___f_5816_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0___boxed as *mut core::ffi::c_void, 15, 7);
                        crate::leanh::lean_closure_set(v___f_5816_, 0, v_fvars_5795_);
                        crate::leanh::lean_closure_set(v___f_5816_, 1, v_pre_5790_);
                        crate::leanh::lean_closure_set(v___f_5816_, 2, v_post_5791_);
                        crate::leanh::lean_closure_set(v___f_5816_, 3, v___x_5813_);
                        crate::leanh::lean_closure_set(v___f_5816_, 4, v___x_5814_);
                        crate::leanh::lean_closure_set(v___f_5816_, 5, v___x_5815_);
                        crate::leanh::lean_closure_set(v___f_5816_, 6, v_body_5806_);
                        v___x_5817_ = 0;
                        v___x_5818_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_binderName_5804_, v_binderInfo_5807_, v_fst_5811_, v___f_5816_, v___x_5817_, v_a_5797_, v_snd_5812_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
                        return v___x_5818_;
                    } else {
                        crate::leanh::lean_dec_ref(v_body_5806_);
                        crate::leanh::lean_dec(v_binderName_5804_);
                        crate::leanh::lean_dec_ref(v_fvars_5795_);
                        crate::leanh::lean_dec_ref(v_post_5791_);
                        crate::leanh::lean_dec_ref(v_pre_5790_);
                        return v___x_5809_;
                    }
                } else {
                    v___x_5819_ = lean_expr_instantiate_rev(v_e_5796_, v_fvars_5795_);
                    crate::leanh::lean_dec_ref(v_e_5796_);
                    crate::leanh::lean_inc_ref(v_post_5791_);
                    crate::leanh::lean_inc_ref(v_pre_5790_);
                    v___x_5820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5790_, v_post_5791_, v_usedLetOnly_5792_, v_skipConstInApp_5793_, v_skipInstances_5794_, v___x_5819_, v_a_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
                    if crate::leanh::lean_obj_tag(v___x_5820_) == 0 {
                        v_a_5821_ = crate::leanh::lean_ctor_get(v___x_5820_, 0);
                        crate::leanh::lean_inc(v_a_5821_);
                        crate::leanh::lean_dec_ref_known(v___x_5820_, 1);
                        v_fst_5822_ = crate::leanh::lean_ctor_get(v_a_5821_, 0);
                        crate::leanh::lean_inc(v_fst_5822_);
                        v_snd_5823_ = crate::leanh::lean_ctor_get(v_a_5821_, 1);
                        crate::leanh::lean_inc(v_snd_5823_);
                        crate::leanh::lean_dec(v_a_5821_);
                        v___x_5824_ = 0;
                        v___x_5825_ = 1;
                        v___x_5826_ = 1;
                        v___x_5827_ = l_Lean_Meta_mkForallFVars(
                            v_fvars_5795_,
                            v_fst_5822_,
                            v___x_5824_,
                            v_usedLetOnly_5792_,
                            v___x_5825_,
                            v___x_5826_,
                            v___y_5799_,
                            v___y_5800_,
                            v___y_5801_,
                            v___y_5802_,
                        );
                        crate::leanh::lean_dec_ref(v_fvars_5795_);
                        if crate::leanh::lean_obj_tag(v___x_5827_) == 0 {
                            v_a_5828_ = crate::leanh::lean_ctor_get(v___x_5827_, 0);
                            crate::leanh::lean_inc(v_a_5828_);
                            crate::leanh::lean_dec_ref_known(v___x_5827_, 1);
                            v___x_5829_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5790_, v_post_5791_, v_usedLetOnly_5792_, v_skipConstInApp_5793_, v_skipInstances_5794_, v_a_5828_, v_a_5797_, v_snd_5823_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
                            return v___x_5829_;
                        } else {
                            crate::leanh::lean_dec(v_snd_5823_);
                            crate::leanh::lean_dec_ref(v_post_5791_);
                            crate::leanh::lean_dec_ref(v_pre_5790_);
                            v_a_5830_ = crate::leanh::lean_ctor_get(v___x_5827_, 0);
                            v_isSharedCheck_5837_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5827_)) as u8;
                            if v_isSharedCheck_5837_ == 0 {
                                v___x_5832_ = v___x_5827_;
                                v_isShared_5833_ = v_isSharedCheck_5837_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5830_);
                                crate::leanh::lean_dec(v___x_5827_);
                                v___x_5832_ = crate::leanh::lean_box(0);
                                v_isShared_5833_ = v_isSharedCheck_5837_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fvars_5795_);
                        crate::leanh::lean_dec_ref(v_post_5791_);
                        crate::leanh::lean_dec_ref(v_pre_5790_);
                        return v___x_5820_;
                    }
                }
            }
            1 => {
                if v_isShared_5833_ == 0 {
                    v___x_5835_ = v___x_5832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5830_);
                    v___x_5835_ = v_reuseFailAlloc_5836_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___lam__0(
    mut v_fvars_5838_: *mut crate::leanh::LeanObject,
    mut v_pre_5839_: *mut crate::leanh::LeanObject,
    mut v_post_5840_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5841_: u8,
    mut v_skipConstInApp_5842_: u8,
    mut v_skipInstances_5843_: u8,
    mut v_body_5844_: *mut crate::leanh::LeanObject,
    mut v_x_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
    mut v___y_5847_: *mut crate::leanh::LeanObject,
    mut v___y_5848_: *mut crate::leanh::LeanObject,
    mut v___y_5849_: *mut crate::leanh::LeanObject,
    mut v___y_5850_: *mut crate::leanh::LeanObject,
    mut v___y_5851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5853_ = lean_array_push(v_fvars_5838_, v_x_5845_);
    v___x_5854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_5839_, v_post_5840_, v_usedLetOnly_5841_, v_skipConstInApp_5842_, v_skipInstances_5843_, v___x_5853_, v_body_5844_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
    return v___x_5854_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8___boxed(
    mut v_pre_5855_: *mut crate::leanh::LeanObject,
    mut v_post_5856_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5857_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5858_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5859_: *mut crate::leanh::LeanObject,
    mut v_sz_5860_: *mut crate::leanh::LeanObject,
    mut v_i_5861_: *mut crate::leanh::LeanObject,
    mut v_bs_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
    mut v___y_5867_: *mut crate::leanh::LeanObject,
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5870_: u8 = 0;
    let mut v_skipConstInApp_boxed_5871_: u8 = 0;
    let mut v_skipInstances_boxed_5872_: u8 = 0;
    let mut v_sz_boxed_5873_: usize = 0;
    let mut v_i_boxed_5874_: usize = 0;
    let mut v_res_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5870_ = (crate::leanh::lean_unbox(v_usedLetOnly_5857_) as u8);
    v_skipConstInApp_boxed_5871_ = (crate::leanh::lean_unbox(v_skipConstInApp_5858_) as u8);
    v_skipInstances_boxed_5872_ = (crate::leanh::lean_unbox(v_skipInstances_5859_) as u8);
    v_sz_boxed_5873_ = crate::leanh::lean_unbox_usize(v_sz_5860_);
    crate::leanh::lean_dec(v_sz_5860_);
    v_i_boxed_5874_ = crate::leanh::lean_unbox_usize(v_i_5861_);
    crate::leanh::lean_dec(v_i_5861_);
    v_res_5875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__8(v_pre_5855_, v_post_5856_, v_usedLetOnly_boxed_5870_, v_skipConstInApp_boxed_5871_, v_skipInstances_boxed_5872_, v_sz_boxed_5873_, v_i_boxed_5874_, v_bs_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_);
    crate::leanh::lean_dec(v___y_5868_);
    crate::leanh::lean_dec_ref(v___y_5867_);
    crate::leanh::lean_dec(v___y_5866_);
    crate::leanh::lean_dec_ref(v___y_5865_);
    crate::leanh::lean_dec(v___y_5863_);
    return v_res_5875_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9___boxed(
    mut v_pre_5876_: *mut crate::leanh::LeanObject,
    mut v_post_5877_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5878_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5879_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5880_: *mut crate::leanh::LeanObject,
    mut v_e_5881_: *mut crate::leanh::LeanObject,
    mut v_a_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5889_: u8 = 0;
    let mut v_skipConstInApp_boxed_5890_: u8 = 0;
    let mut v_skipInstances_boxed_5891_: u8 = 0;
    let mut v_res_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5889_ = (crate::leanh::lean_unbox(v_usedLetOnly_5878_) as u8);
    v_skipConstInApp_boxed_5890_ = (crate::leanh::lean_unbox(v_skipConstInApp_5879_) as u8);
    v_skipInstances_boxed_5891_ = (crate::leanh::lean_unbox(v_skipInstances_5880_) as u8);
    v_res_5892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__9(v_pre_5876_, v_post_5877_, v_usedLetOnly_boxed_5889_, v_skipConstInApp_boxed_5890_, v_skipInstances_boxed_5891_, v_e_5881_, v_a_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_);
    crate::leanh::lean_dec(v___y_5887_);
    crate::leanh::lean_dec_ref(v___y_5886_);
    crate::leanh::lean_dec(v___y_5885_);
    crate::leanh::lean_dec_ref(v___y_5884_);
    crate::leanh::lean_dec(v_a_5882_);
    return v_res_5892_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12___boxed(
    mut v_pre_5893_: *mut crate::leanh::LeanObject,
    mut v_post_5894_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5895_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5896_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5897_: *mut crate::leanh::LeanObject,
    mut v_fvars_5898_: *mut crate::leanh::LeanObject,
    mut v_e_5899_: *mut crate::leanh::LeanObject,
    mut v_a_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
    mut v___y_5903_: *mut crate::leanh::LeanObject,
    mut v___y_5904_: *mut crate::leanh::LeanObject,
    mut v___y_5905_: *mut crate::leanh::LeanObject,
    mut v___y_5906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5907_: u8 = 0;
    let mut v_skipConstInApp_boxed_5908_: u8 = 0;
    let mut v_skipInstances_boxed_5909_: u8 = 0;
    let mut v_res_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5907_ = (crate::leanh::lean_unbox(v_usedLetOnly_5895_) as u8);
    v_skipConstInApp_boxed_5908_ = (crate::leanh::lean_unbox(v_skipConstInApp_5896_) as u8);
    v_skipInstances_boxed_5909_ = (crate::leanh::lean_unbox(v_skipInstances_5897_) as u8);
    v_res_5910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12(v_pre_5893_, v_post_5894_, v_usedLetOnly_boxed_5907_, v_skipConstInApp_boxed_5908_, v_skipInstances_boxed_5909_, v_fvars_5898_, v_e_5899_, v_a_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_);
    crate::leanh::lean_dec(v___y_5905_);
    crate::leanh::lean_dec_ref(v___y_5904_);
    crate::leanh::lean_dec(v___y_5903_);
    crate::leanh::lean_dec_ref(v___y_5902_);
    crate::leanh::lean_dec(v_a_5900_);
    return v_res_5910_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13___boxed(
    mut v_pre_5911_: *mut crate::leanh::LeanObject,
    mut v_post_5912_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5913_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5914_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5915_: *mut crate::leanh::LeanObject,
    mut v_fvars_5916_: *mut crate::leanh::LeanObject,
    mut v_e_5917_: *mut crate::leanh::LeanObject,
    mut v_a_5918_: *mut crate::leanh::LeanObject,
    mut v___y_5919_: *mut crate::leanh::LeanObject,
    mut v___y_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5925_: u8 = 0;
    let mut v_skipConstInApp_boxed_5926_: u8 = 0;
    let mut v_skipInstances_boxed_5927_: u8 = 0;
    let mut v_res_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5925_ = (crate::leanh::lean_unbox(v_usedLetOnly_5913_) as u8);
    v_skipConstInApp_boxed_5926_ = (crate::leanh::lean_unbox(v_skipConstInApp_5914_) as u8);
    v_skipInstances_boxed_5927_ = (crate::leanh::lean_unbox(v_skipInstances_5915_) as u8);
    v_res_5928_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__13(v_pre_5911_, v_post_5912_, v_usedLetOnly_boxed_5925_, v_skipConstInApp_boxed_5926_, v_skipInstances_boxed_5927_, v_fvars_5916_, v_e_5917_, v_a_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_);
    crate::leanh::lean_dec(v___y_5923_);
    crate::leanh::lean_dec_ref(v___y_5922_);
    crate::leanh::lean_dec(v___y_5921_);
    crate::leanh::lean_dec_ref(v___y_5920_);
    crate::leanh::lean_dec(v_a_5918_);
    return v_res_5928_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4___boxed(
    mut v_pre_5929_: *mut crate::leanh::LeanObject,
    mut v_post_5930_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5931_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5932_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5933_: *mut crate::leanh::LeanObject,
    mut v_e_5934_: *mut crate::leanh::LeanObject,
    mut v_a_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
    mut v___y_5937_: *mut crate::leanh::LeanObject,
    mut v___y_5938_: *mut crate::leanh::LeanObject,
    mut v___y_5939_: *mut crate::leanh::LeanObject,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5942_: u8 = 0;
    let mut v_skipConstInApp_boxed_5943_: u8 = 0;
    let mut v_skipInstances_boxed_5944_: u8 = 0;
    let mut v_res_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5942_ = (crate::leanh::lean_unbox(v_usedLetOnly_5931_) as u8);
    v_skipConstInApp_boxed_5943_ = (crate::leanh::lean_unbox(v_skipConstInApp_5932_) as u8);
    v_skipInstances_boxed_5944_ = (crate::leanh::lean_unbox(v_skipInstances_5933_) as u8);
    v_res_5945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_5929_, v_post_5930_, v_usedLetOnly_boxed_5942_, v_skipConstInApp_boxed_5943_, v_skipInstances_boxed_5944_, v_e_5934_, v_a_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
    crate::leanh::lean_dec(v___y_5940_);
    crate::leanh::lean_dec_ref(v___y_5939_);
    crate::leanh::lean_dec(v___y_5938_);
    crate::leanh::lean_dec_ref(v___y_5937_);
    crate::leanh::lean_dec(v_a_5935_);
    return v_res_5945_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14___boxed(
    mut v_pre_5946_: *mut crate::leanh::LeanObject,
    mut v_post_5947_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5948_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5949_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5950_: *mut crate::leanh::LeanObject,
    mut v_fvars_5951_: *mut crate::leanh::LeanObject,
    mut v_e_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
    mut v___y_5954_: *mut crate::leanh::LeanObject,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
    mut v___y_5958_: *mut crate::leanh::LeanObject,
    mut v___y_5959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5960_: u8 = 0;
    let mut v_skipConstInApp_boxed_5961_: u8 = 0;
    let mut v_skipInstances_boxed_5962_: u8 = 0;
    let mut v_res_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5960_ = (crate::leanh::lean_unbox(v_usedLetOnly_5948_) as u8);
    v_skipConstInApp_boxed_5961_ = (crate::leanh::lean_unbox(v_skipConstInApp_5949_) as u8);
    v_skipInstances_boxed_5962_ = (crate::leanh::lean_unbox(v_skipInstances_5950_) as u8);
    v_res_5963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14(v_pre_5946_, v_post_5947_, v_usedLetOnly_boxed_5960_, v_skipConstInApp_boxed_5961_, v_skipInstances_boxed_5962_, v_fvars_5951_, v_e_5952_, v_a_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_);
    crate::leanh::lean_dec(v___y_5958_);
    crate::leanh::lean_dec_ref(v___y_5957_);
    crate::leanh::lean_dec(v___y_5956_);
    crate::leanh::lean_dec_ref(v___y_5955_);
    crate::leanh::lean_dec(v_a_5953_);
    return v_res_5963_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg___boxed(
    mut v_upperBound_5964_: *mut crate::leanh::LeanObject,
    mut v___x_5965_: *mut crate::leanh::LeanObject,
    mut v_pre_5966_: *mut crate::leanh::LeanObject,
    mut v_post_5967_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5968_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5969_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_5970_: *mut crate::leanh::LeanObject,
    mut v_a_5971_: *mut crate::leanh::LeanObject,
    mut v_b_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
    mut v___y_5975_: *mut crate::leanh::LeanObject,
    mut v___y_5976_: *mut crate::leanh::LeanObject,
    mut v___y_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_5980_: u8 = 0;
    let mut v_skipConstInApp_boxed_5981_: u8 = 0;
    let mut v_skipInstances_boxed_5982_: u8 = 0;
    let mut v_res_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_5980_ = (crate::leanh::lean_unbox(v_usedLetOnly_5968_) as u8);
    v_skipConstInApp_boxed_5981_ = (crate::leanh::lean_unbox(v_skipConstInApp_5969_) as u8);
    v_skipInstances_boxed_5982_ = (crate::leanh::lean_unbox(v_skipInstances_5970_) as u8);
    v_res_5983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_5964_, v___x_5965_, v_pre_5966_, v_post_5967_, v_usedLetOnly_boxed_5980_, v_skipConstInApp_boxed_5981_, v_skipInstances_boxed_5982_, v_a_5971_, v_b_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
    crate::leanh::lean_dec(v___y_5978_);
    crate::leanh::lean_dec_ref(v___y_5977_);
    crate::leanh::lean_dec(v___y_5976_);
    crate::leanh::lean_dec_ref(v___y_5975_);
    crate::leanh::lean_dec(v___y_5973_);
    crate::leanh::lean_dec_ref(v___x_5965_);
    crate::leanh::lean_dec(v_upperBound_5964_);
    return v_res_5983_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15___boxed(
    mut v_skipInstances_5984_: *mut crate::leanh::LeanObject,
    mut v_pre_5985_: *mut crate::leanh::LeanObject,
    mut v_post_5986_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_5987_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_5988_: *mut crate::leanh::LeanObject,
    mut v_x_5989_: *mut crate::leanh::LeanObject,
    mut v_x_5990_: *mut crate::leanh::LeanObject,
    mut v_x_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipInstances_boxed_5999_: u8 = 0;
    let mut v_usedLetOnly_boxed_6000_: u8 = 0;
    let mut v_skipConstInApp_boxed_6001_: u8 = 0;
    let mut v_res_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_5999_ = (crate::leanh::lean_unbox(v_skipInstances_5984_) as u8);
    v_usedLetOnly_boxed_6000_ = (crate::leanh::lean_unbox(v_usedLetOnly_5987_) as u8);
    v_skipConstInApp_boxed_6001_ = (crate::leanh::lean_unbox(v_skipConstInApp_5988_) as u8);
    v_res_6002_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__15(v_skipInstances_boxed_5999_, v_pre_5985_, v_post_5986_, v_usedLetOnly_boxed_6000_, v_skipConstInApp_boxed_6001_, v_x_5989_, v_x_5990_, v_x_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_);
    crate::leanh::lean_dec(v___y_5997_);
    crate::leanh::lean_dec_ref(v___y_5996_);
    crate::leanh::lean_dec(v___y_5995_);
    crate::leanh::lean_dec_ref(v___y_5994_);
    crate::leanh::lean_dec(v___y_5992_);
    return v_res_6002_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(
    mut v_00_u03b1_6003_: *mut crate::leanh::LeanObject,
    mut v_x_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6011_ = crate::leanh::lean_apply_1(v_x_6004_, crate::leanh::lean_box(0));
    v___x_6012_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6012_, 0, v___x_6011_);
    crate::leanh::lean_ctor_set(v___x_6012_, 1, v___y_6005_);
    v___x_6013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6013_, 0, v___x_6012_);
    return v___x_6013_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0___boxed(
    mut v_00_u03b1_6014_: *mut crate::leanh::LeanObject,
    mut v_x_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
    mut v___y_6019_: *mut crate::leanh::LeanObject,
    mut v___y_6020_: *mut crate::leanh::LeanObject,
    mut v___y_6021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6022_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(
        v_00_u03b1_6014_,
        v_x_6015_,
        v___y_6016_,
        v___y_6017_,
        v___y_6018_,
        v___y_6019_,
        v___y_6020_,
    );
    crate::leanh::lean_dec(v___y_6020_);
    crate::leanh::lean_dec_ref(v___y_6019_);
    crate::leanh::lean_dec(v___y_6018_);
    crate::leanh::lean_dec_ref(v___y_6017_);
    return v_res_6022_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6023_ = crate::leanh::lean_box(0);
    v___x_6024_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_6025_ = lean_mk_array(v___x_6024_, v___x_6023_);
    return v___x_6025_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__0,
    );
    v___x_6027_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6028_, 0, v___x_6027_);
    crate::leanh::lean_ctor_set(v___x_6028_, 1, v___x_6026_);
    return v___x_6028_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__1,
    );
    v___x_6030_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_6030_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6030_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6030_, 2, v___x_6029_);
    return v___x_6030_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(
    mut v_input_6031_: *mut crate::leanh::LeanObject,
    mut v_pre_6032_: *mut crate::leanh::LeanObject,
    mut v_post_6033_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6034_: u8,
    mut v_skipConstInApp_6035_: u8,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
    mut v___y_6037_: *mut crate::leanh::LeanObject,
    mut v___y_6038_: *mut crate::leanh::LeanObject,
    mut v___y_6039_: *mut crate::leanh::LeanObject,
    mut v___y_6040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: u8 = 0;
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6057_: u8 = 0;
    let mut v_snd_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6068_: u8 = 0;
    let mut v_unused_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6042_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2_once
                    ),
                    _init_l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___closed__2,
                );
                v___x_6043_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(
                    crate::leanh::lean_box(0),
                    v___x_6042_,
                    v___y_6036_,
                    v___y_6037_,
                    v___y_6038_,
                    v___y_6039_,
                    v___y_6040_,
                );
                v_a_6044_ = crate::leanh::lean_ctor_get(v___x_6043_, 0);
                crate::leanh::lean_inc(v_a_6044_);
                crate::leanh::lean_dec_ref(v___x_6043_);
                v_fst_6045_ = crate::leanh::lean_ctor_get(v_a_6044_, 0);
                crate::leanh::lean_inc(v_fst_6045_);
                v_snd_6046_ = crate::leanh::lean_ctor_get(v_a_6044_, 1);
                crate::leanh::lean_inc(v_snd_6046_);
                crate::leanh::lean_dec(v_a_6044_);
                v___x_6047_ = 0;
                v___x_6048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4(v_pre_6032_, v_post_6033_, v_usedLetOnly_6034_, v_skipConstInApp_6035_, v___x_6047_, v_input_6031_, v_fst_6045_, v_snd_6046_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
                if crate::leanh::lean_obj_tag(v___x_6048_) == 0 {
                    v_a_6049_ = crate::leanh::lean_ctor_get(v___x_6048_, 0);
                    crate::leanh::lean_inc(v_a_6049_);
                    crate::leanh::lean_dec_ref_known(v___x_6048_, 1);
                    v_fst_6050_ = crate::leanh::lean_ctor_get(v_a_6049_, 0);
                    crate::leanh::lean_inc(v_fst_6050_);
                    v_snd_6051_ = crate::leanh::lean_ctor_get(v_a_6049_, 1);
                    crate::leanh::lean_inc(v_snd_6051_);
                    crate::leanh::lean_dec(v_a_6049_);
                    v___x_6052_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_6052_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_6052_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_6052_, 2, v_fst_6045_);
                    v___x_6053_ =
                        l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___lam__0(
                            crate::leanh::lean_box(0),
                            v___x_6052_,
                            v_snd_6051_,
                            v___y_6037_,
                            v___y_6038_,
                            v___y_6039_,
                            v___y_6040_,
                        );
                    v_a_6054_ = crate::leanh::lean_ctor_get(v___x_6053_, 0);
                    v_isSharedCheck_6070_ = (!crate::leanh::lean_is_exclusive(v___x_6053_)) as u8;
                    if v_isSharedCheck_6070_ == 0 {
                        v___x_6056_ = v___x_6053_;
                        v_isShared_6057_ = v_isSharedCheck_6070_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6054_);
                        crate::leanh::lean_dec(v___x_6053_);
                        v___x_6056_ = crate::leanh::lean_box(0);
                        v_isShared_6057_ = v_isSharedCheck_6070_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6045_);
                    return v___x_6048_;
                }
            }
            1 => {
                v_snd_6058_ = crate::leanh::lean_ctor_get(v_a_6054_, 1);
                v_isSharedCheck_6068_ = (!crate::leanh::lean_is_exclusive(v_a_6054_)) as u8;
                if v_isSharedCheck_6068_ == 0 {
                    v_unused_6069_ = crate::leanh::lean_ctor_get(v_a_6054_, 0);
                    crate::leanh::lean_dec(v_unused_6069_);
                    v___x_6060_ = v_a_6054_;
                    v_isShared_6061_ = v_isSharedCheck_6068_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6058_);
                    crate::leanh::lean_dec(v_a_6054_);
                    v___x_6060_ = crate::leanh::lean_box(0);
                    v_isShared_6061_ = v_isSharedCheck_6068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6060_, 0, v_fst_6050_);
                    v___x_6063_ = v___x_6060_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6067_, 0, v_fst_6050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6067_, 1, v_snd_6058_);
                    v___x_6063_ = v_reuseFailAlloc_6067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6057_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6056_, 0, v___x_6063_);
                    v___x_6065_ = v___x_6056_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6066_, 0, v___x_6063_);
                    v___x_6065_ = v_reuseFailAlloc_6066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1___boxed(
    mut v_input_6071_: *mut crate::leanh::LeanObject,
    mut v_pre_6072_: *mut crate::leanh::LeanObject,
    mut v_post_6073_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6074_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6082_: u8 = 0;
    let mut v_skipConstInApp_boxed_6083_: u8 = 0;
    let mut v_res_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6082_ = (crate::leanh::lean_unbox(v_usedLetOnly_6074_) as u8);
    v_skipConstInApp_boxed_6083_ = (crate::leanh::lean_unbox(v_skipConstInApp_6075_) as u8);
    v_res_6084_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(
        v_input_6071_,
        v_pre_6072_,
        v_post_6073_,
        v_usedLetOnly_boxed_6082_,
        v_skipConstInApp_boxed_6083_,
        v___y_6076_,
        v___y_6077_,
        v___y_6078_,
        v___y_6079_,
        v___y_6080_,
    );
    crate::leanh::lean_dec(v___y_6080_);
    crate::leanh::lean_dec_ref(v___y_6079_);
    crate::leanh::lean_dec(v___y_6078_);
    crate::leanh::lean_dec_ref(v___y_6077_);
    return v_res_6084_;
}
pub unsafe fn _init_l_Lean_Meta_expandCoe___closed__2() -> u64 {
    let mut v___x_6087_: u8 = 0;
    let mut v___x_6088_: u64 = 0;
    v___x_6087_ = 3;
    v___x_6088_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_6087_);
    return v___x_6088_;
}
pub unsafe fn l_Lean_Meta_expandCoe(
    mut v_e_6089_: *mut crate::leanh::LeanObject,
    mut v_a_6090_: *mut crate::leanh::LeanObject,
    mut v_a_6091_: *mut crate::leanh::LeanObject,
    mut v_a_6092_: *mut crate::leanh::LeanObject,
    mut v_a_6093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_6096_: u8 = 0;
    let mut v_ctxApprox_6097_: u8 = 0;
    let mut v_quasiPatternApprox_6098_: u8 = 0;
    let mut v_constApprox_6099_: u8 = 0;
    let mut v_isDefEqStuckEx_6100_: u8 = 0;
    let mut v_unificationHints_6101_: u8 = 0;
    let mut v_proofIrrelevance_6102_: u8 = 0;
    let mut v_assignSyntheticOpaque_6103_: u8 = 0;
    let mut v_offsetCnstrs_6104_: u8 = 0;
    let mut v_etaStruct_6105_: u8 = 0;
    let mut v_univApprox_6106_: u8 = 0;
    let mut v_iota_6107_: u8 = 0;
    let mut v_beta_6108_: u8 = 0;
    let mut v_proj_6109_: u8 = 0;
    let mut v_zeta_6110_: u8 = 0;
    let mut v_zetaDelta_6111_: u8 = 0;
    let mut v_zetaUnused_6112_: u8 = 0;
    let mut v_zetaHave_6113_: u8 = 0;
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6116_: u8 = 0;
    let mut v_trackZetaDelta_6117_: u8 = 0;
    let mut v_zetaDeltaSet_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6124_: u8 = 0;
    let mut v_inTypeClassResolution_6125_: u8 = 0;
    let mut v_cacheInferType_6126_: u8 = 0;
    let mut v___x_6127_: u8 = 0;
    let mut v_config_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: u64 = 0;
    let mut v___x_6131_: u64 = 0;
    let mut v___x_6132_: u64 = 0;
    let mut v___f_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: u8 = 0;
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: u64 = 0;
    let mut v___x_6138_: u64 = 0;
    let mut v_key_6139_: u64 = 0;
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6095_ = l_Lean_Meta_Context_config(v_a_6090_);
                v_foApprox_6096_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 0 as u32);
                v_ctxApprox_6097_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 1 as u32);
                v_quasiPatternApprox_6098_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_6095_, 2 as u32);
                v_constApprox_6099_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 3 as u32);
                v_isDefEqStuckEx_6100_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 4 as u32);
                v_unificationHints_6101_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 5 as u32);
                v_proofIrrelevance_6102_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 6 as u32);
                v_assignSyntheticOpaque_6103_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_6095_, 7 as u32);
                v_offsetCnstrs_6104_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 8 as u32);
                v_etaStruct_6105_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 10 as u32);
                v_univApprox_6106_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 11 as u32);
                v_iota_6107_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 12 as u32);
                v_beta_6108_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 13 as u32);
                v_proj_6109_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 14 as u32);
                v_zeta_6110_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 15 as u32);
                v_zetaDelta_6111_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 16 as u32);
                v_zetaUnused_6112_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 17 as u32);
                v_zetaHave_6113_ = crate::leanh::lean_ctor_get_uint8(v___x_6095_, 18 as u32);
                v_isSharedCheck_6144_ = (!crate::leanh::lean_is_exclusive(v___x_6095_)) as u8;
                if v_isSharedCheck_6144_ == 0 {
                    v___x_6115_ = v___x_6095_;
                    v_isShared_6116_ = v_isSharedCheck_6144_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6095_);
                    v___x_6115_ = crate::leanh::lean_box(0);
                    v_isShared_6116_ = v_isSharedCheck_6144_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_6117_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6090_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_6118_ = crate::leanh::lean_ctor_get(v_a_6090_, 1);
                v_lctx_6119_ = crate::leanh::lean_ctor_get(v_a_6090_, 2);
                v_localInstances_6120_ = crate::leanh::lean_ctor_get(v_a_6090_, 3);
                v_defEqCtx_x3f_6121_ = crate::leanh::lean_ctor_get(v_a_6090_, 4);
                v_synthPendingDepth_6122_ = crate::leanh::lean_ctor_get(v_a_6090_, 5);
                v_canUnfold_x3f_6123_ = crate::leanh::lean_ctor_get(v_a_6090_, 6);
                v_univApprox_6124_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6090_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_6125_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6090_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_6126_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6090_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_6127_ = 3;
                if v_isShared_6116_ == 0 {
                    v_config_6129_ = v___x_6115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6143_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        0 as u32,
                        v_foApprox_6096_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        1 as u32,
                        v_ctxApprox_6097_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        2 as u32,
                        v_quasiPatternApprox_6098_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        3 as u32,
                        v_constApprox_6099_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        4 as u32,
                        v_isDefEqStuckEx_6100_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        5 as u32,
                        v_unificationHints_6101_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        6 as u32,
                        v_proofIrrelevance_6102_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        7 as u32,
                        v_assignSyntheticOpaque_6103_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        8 as u32,
                        v_offsetCnstrs_6104_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        10 as u32,
                        v_etaStruct_6105_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        11 as u32,
                        v_univApprox_6106_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        12 as u32,
                        v_iota_6107_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        13 as u32,
                        v_beta_6108_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        14 as u32,
                        v_proj_6109_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        15 as u32,
                        v_zeta_6110_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        16 as u32,
                        v_zetaDelta_6111_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        17 as u32,
                        v_zetaUnused_6112_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6143_,
                        18 as u32,
                        v_zetaHave_6113_,
                    );
                    v_config_6129_ = v_reuseFailAlloc_6143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_6129_, 9 as u32, v___x_6127_);
                v___x_6130_ = l_Lean_Meta_Context_configKey(v_a_6090_);
                v___x_6131_ = 3u64;
                v___x_6132_ = lean_uint64_shift_right(v___x_6130_, v___x_6131_);
                v___f_6133_ = l_Lean_Meta_expandCoe___closed__0;
                v___f_6134_ = l_Lean_Meta_expandCoe___closed__1;
                v___x_6135_ = 0;
                v___x_6136_ = crate::leanh::lean_box(0);
                v___x_6137_ = lean_uint64_shift_left(v___x_6132_, v___x_6131_);
                v___x_6138_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_expandCoe___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_expandCoe___closed__2_once),
                    _init_l_Lean_Meta_expandCoe___closed__2,
                );
                v_key_6139_ = lean_uint64_lor(v___x_6137_, v___x_6138_);
                v___x_6140_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_6140_, 0, v_config_6129_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_6140_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_6139_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_6123_);
                crate::leanh::lean_inc(v_synthPendingDepth_6122_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_6121_);
                crate::leanh::lean_inc_ref(v_localInstances_6120_);
                crate::leanh::lean_inc_ref(v_lctx_6119_);
                crate::leanh::lean_inc(v_zetaDeltaSet_6118_);
                v___x_6141_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_6141_, 0, v___x_6140_);
                crate::leanh::lean_ctor_set(v___x_6141_, 1, v_zetaDeltaSet_6118_);
                crate::leanh::lean_ctor_set(v___x_6141_, 2, v_lctx_6119_);
                crate::leanh::lean_ctor_set(v___x_6141_, 3, v_localInstances_6120_);
                crate::leanh::lean_ctor_set(v___x_6141_, 4, v_defEqCtx_x3f_6121_);
                crate::leanh::lean_ctor_set(v___x_6141_, 5, v_synthPendingDepth_6122_);
                crate::leanh::lean_ctor_set(v___x_6141_, 6, v_canUnfold_x3f_6123_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_6117_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_6124_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_6125_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_6126_,
                );
                v___x_6142_ = l_Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1(
                    v_e_6089_,
                    v___f_6134_,
                    v___f_6133_,
                    v___x_6135_,
                    v___x_6135_,
                    v___x_6136_,
                    v___x_6141_,
                    v_a_6091_,
                    v_a_6092_,
                    v_a_6093_,
                );
                crate::leanh::lean_dec_ref_known(v___x_6141_, 7);
                return v___x_6142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_expandCoe___boxed(
    mut v_e_6145_: *mut crate::leanh::LeanObject,
    mut v_a_6146_: *mut crate::leanh::LeanObject,
    mut v_a_6147_: *mut crate::leanh::LeanObject,
    mut v_a_6148_: *mut crate::leanh::LeanObject,
    mut v_a_6149_: *mut crate::leanh::LeanObject,
    mut v_a_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6151_ = l_Lean_Meta_expandCoe(v_e_6145_, v_a_6146_, v_a_6147_, v_a_6148_, v_a_6149_);
    crate::leanh::lean_dec(v_a_6149_);
    crate::leanh::lean_dec_ref(v_a_6148_);
    crate::leanh::lean_dec(v_a_6147_);
    crate::leanh::lean_dec_ref(v_a_6146_);
    return v_res_6151_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(
    mut v_00_u03b2_6152_: *mut crate::leanh::LeanObject,
    mut v_m_6153_: *mut crate::leanh::LeanObject,
    mut v_a_6154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___redArg(v_m_6153_, v_a_6154_);
    return v___x_6155_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2___boxed(
    mut v_00_u03b2_6156_: *mut crate::leanh::LeanObject,
    mut v_m_6157_: *mut crate::leanh::LeanObject,
    mut v_a_6158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2(v_00_u03b2_6156_, v_m_6157_, v_a_6158_);
    crate::leanh::lean_dec(v_a_6158_);
    crate::leanh::lean_dec_ref(v_m_6157_);
    return v_res_6159_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6160_: *mut crate::leanh::LeanObject,
    mut v_x_6161_: *mut crate::leanh::LeanObject,
    mut v_x_6162_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6163_: u8 = 0;
    v___x_6163_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___redArg(v_x_6161_, v_x_6162_);
    return v___x_6163_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_6164_: *mut crate::leanh::LeanObject,
    mut v_x_6165_: *mut crate::leanh::LeanObject,
    mut v_x_6166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6167_: u8 = 0;
    let mut v_r_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6167_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1(v_00_u03b2_6164_, v_x_6165_, v_x_6166_);
    crate::leanh::lean_dec_ref(v_x_6166_);
    crate::leanh::lean_dec_ref(v_x_6165_);
    v_r_6168_ = crate::leanh::lean_box((v_res_6167_) as usize);
    return v_r_6168_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(
    mut v_00_u03b2_6169_: *mut crate::leanh::LeanObject,
    mut v_a_6170_: *mut crate::leanh::LeanObject,
    mut v_x_6171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6172_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___redArg(v_a_6170_, v_x_6171_);
    return v___x_6172_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_6173_: *mut crate::leanh::LeanObject,
    mut v_a_6174_: *mut crate::leanh::LeanObject,
    mut v_x_6175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__2_spec__5(v_00_u03b2_6173_, v_a_6174_, v_x_6175_);
    crate::leanh::lean_dec(v_x_6175_);
    crate::leanh::lean_dec(v_a_6174_);
    return v_res_6176_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(
    mut v_upperBound_6177_: *mut crate::leanh::LeanObject,
    mut v___x_6178_: *mut crate::leanh::LeanObject,
    mut v_pre_6179_: *mut crate::leanh::LeanObject,
    mut v_post_6180_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6181_: u8,
    mut v_skipConstInApp_6182_: u8,
    mut v_skipInstances_6183_: u8,
    mut v___x_6184_: *mut crate::leanh::LeanObject,
    mut v_inst_6185_: *mut crate::leanh::LeanObject,
    mut v_R_6186_: *mut crate::leanh::LeanObject,
    mut v_a_6187_: *mut crate::leanh::LeanObject,
    mut v_b_6188_: *mut crate::leanh::LeanObject,
    mut v_c_6189_: *mut crate::leanh::LeanObject,
    mut v___y_6190_: *mut crate::leanh::LeanObject,
    mut v___y_6191_: *mut crate::leanh::LeanObject,
    mut v___y_6192_: *mut crate::leanh::LeanObject,
    mut v___y_6193_: *mut crate::leanh::LeanObject,
    mut v___y_6194_: *mut crate::leanh::LeanObject,
    mut v___y_6195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___redArg(v_upperBound_6177_, v___x_6178_, v_pre_6179_, v_post_6180_, v_usedLetOnly_6181_, v_skipConstInApp_6182_, v_skipInstances_6183_, v_a_6187_, v_b_6188_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_);
    return v___x_6197_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_6198_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_6199_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_pre_6200_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_post_6201_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_usedLetOnly_6202_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_skipConstInApp_6203_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_skipInstances_6204_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_6205_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_6206_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_R_6207_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_6208_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_b_6209_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_c_6210_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6211_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6212_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6213_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6214_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6215_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6216_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_6217_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_usedLetOnly_boxed_6218_: u8 = 0;
    let mut v_skipConstInApp_boxed_6219_: u8 = 0;
    let mut v_skipInstances_boxed_6220_: u8 = 0;
    let mut v_res_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6218_ = (crate::leanh::lean_unbox(v_usedLetOnly_6202_) as u8);
    v_skipConstInApp_boxed_6219_ = (crate::leanh::lean_unbox(v_skipConstInApp_6203_) as u8);
    v_skipInstances_boxed_6220_ = (crate::leanh::lean_unbox(v_skipInstances_6204_) as u8);
    v_res_6221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__10(v_upperBound_6198_, v___x_6199_, v_pre_6200_, v_post_6201_, v_usedLetOnly_boxed_6218_, v_skipConstInApp_boxed_6219_, v_skipInstances_boxed_6220_, v___x_6205_, v_inst_6206_, v_R_6207_, v_a_6208_, v_b_6209_, v_c_6210_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_);
    crate::leanh::lean_dec(v___y_6216_);
    crate::leanh::lean_dec_ref(v___y_6215_);
    crate::leanh::lean_dec(v___y_6214_);
    crate::leanh::lean_dec_ref(v___y_6213_);
    crate::leanh::lean_dec(v___y_6211_);
    crate::leanh::lean_dec(v___x_6205_);
    crate::leanh::lean_dec_ref(v___x_6199_);
    crate::leanh::lean_dec(v_upperBound_6198_);
    return v_res_6221_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(
    mut v_00_u03b2_6222_: *mut crate::leanh::LeanObject,
    mut v_m_6223_: *mut crate::leanh::LeanObject,
    mut v_a_6224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___redArg(v_m_6223_, v_a_6224_);
    return v___x_6225_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11___boxed(
    mut v_00_u03b2_6226_: *mut crate::leanh::LeanObject,
    mut v_m_6227_: *mut crate::leanh::LeanObject,
    mut v_a_6228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11(v_00_u03b2_6226_, v_m_6227_, v_a_6228_);
    crate::leanh::lean_dec_ref(v_a_6228_);
    crate::leanh::lean_dec_ref(v_m_6227_);
    return v_res_6229_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(
    mut v_00_u03b1_6230_: *mut crate::leanh::LeanObject,
    mut v_name_6231_: *mut crate::leanh::LeanObject,
    mut v_bi_6232_: u8,
    mut v_type_6233_: *mut crate::leanh::LeanObject,
    mut v_k_6234_: *mut crate::leanh::LeanObject,
    mut v_kind_6235_: u8,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6243_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___redArg(v_name_6231_, v_bi_6232_, v_type_6233_, v_k_6234_, v_kind_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
    return v___x_6243_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16___boxed(
    mut v_00_u03b1_6244_: *mut crate::leanh::LeanObject,
    mut v_name_6245_: *mut crate::leanh::LeanObject,
    mut v_bi_6246_: *mut crate::leanh::LeanObject,
    mut v_type_6247_: *mut crate::leanh::LeanObject,
    mut v_k_6248_: *mut crate::leanh::LeanObject,
    mut v_kind_6249_: *mut crate::leanh::LeanObject,
    mut v___y_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_6257_: u8 = 0;
    let mut v_kind_boxed_6258_: u8 = 0;
    let mut v_res_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6257_ = (crate::leanh::lean_unbox(v_bi_6246_) as u8);
    v_kind_boxed_6258_ = (crate::leanh::lean_unbox(v_kind_6249_) as u8);
    v_res_6259_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__12_spec__16(v_00_u03b1_6244_, v_name_6245_, v_bi_boxed_6257_, v_type_6247_, v_k_6248_, v_kind_boxed_6258_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
    crate::leanh::lean_dec(v___y_6255_);
    crate::leanh::lean_dec_ref(v___y_6254_);
    crate::leanh::lean_dec(v___y_6253_);
    crate::leanh::lean_dec_ref(v___y_6252_);
    crate::leanh::lean_dec(v___y_6250_);
    return v_res_6259_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(
    mut v_00_u03b1_6260_: *mut crate::leanh::LeanObject,
    mut v_name_6261_: *mut crate::leanh::LeanObject,
    mut v_type_6262_: *mut crate::leanh::LeanObject,
    mut v_val_6263_: *mut crate::leanh::LeanObject,
    mut v_k_6264_: *mut crate::leanh::LeanObject,
    mut v_nondep_6265_: u8,
    mut v_kind_6266_: u8,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
    mut v___y_6269_: *mut crate::leanh::LeanObject,
    mut v___y_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6274_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___redArg(v_name_6261_, v_type_6262_, v_val_6263_, v_k_6264_, v_nondep_6265_, v_kind_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
    return v___x_6274_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19___boxed(
    mut v_00_u03b1_6275_: *mut crate::leanh::LeanObject,
    mut v_name_6276_: *mut crate::leanh::LeanObject,
    mut v_type_6277_: *mut crate::leanh::LeanObject,
    mut v_val_6278_: *mut crate::leanh::LeanObject,
    mut v_k_6279_: *mut crate::leanh::LeanObject,
    mut v_nondep_6280_: *mut crate::leanh::LeanObject,
    mut v_kind_6281_: *mut crate::leanh::LeanObject,
    mut v___y_6282_: *mut crate::leanh::LeanObject,
    mut v___y_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_6289_: u8 = 0;
    let mut v_kind_boxed_6290_: u8 = 0;
    let mut v_res_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6289_ = (crate::leanh::lean_unbox(v_nondep_6280_) as u8);
    v_kind_boxed_6290_ = (crate::leanh::lean_unbox(v_kind_6281_) as u8);
    v_res_6291_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__14_spec__19(v_00_u03b1_6275_, v_name_6276_, v_type_6277_, v_val_6278_, v_k_6279_, v_nondep_boxed_6289_, v_kind_boxed_6290_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
    crate::leanh::lean_dec(v___y_6287_);
    crate::leanh::lean_dec_ref(v___y_6286_);
    crate::leanh::lean_dec(v___y_6285_);
    crate::leanh::lean_dec_ref(v___y_6284_);
    crate::leanh::lean_dec(v___y_6282_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(
    mut v_00_u03b1_6292_: *mut crate::leanh::LeanObject,
    mut v_ref_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6299_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___redArg(v_ref_6293_);
    return v___x_6299_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22___boxed(
    mut v_00_u03b1_6300_: *mut crate::leanh::LeanObject,
    mut v_ref_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
    mut v___y_6303_: *mut crate::leanh::LeanObject,
    mut v___y_6304_: *mut crate::leanh::LeanObject,
    mut v___y_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6307_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16_spec__22(v_00_u03b1_6300_, v_ref_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
    crate::leanh::lean_dec(v___y_6305_);
    crate::leanh::lean_dec_ref(v___y_6304_);
    crate::leanh::lean_dec(v___y_6303_);
    crate::leanh::lean_dec_ref(v___y_6302_);
    return v_res_6307_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(
    mut v_00_u03b1_6308_: *mut crate::leanh::LeanObject,
    mut v_x_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
    mut v___y_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6317_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___redArg(v_x_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_);
    return v___x_6317_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16___boxed(
    mut v_00_u03b1_6318_: *mut crate::leanh::LeanObject,
    mut v_x_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6327_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__16(v_00_u03b1_6318_, v_x_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_);
    crate::leanh::lean_dec(v___y_6325_);
    crate::leanh::lean_dec_ref(v___y_6324_);
    crate::leanh::lean_dec(v___y_6323_);
    crate::leanh::lean_dec_ref(v___y_6322_);
    crate::leanh::lean_dec(v___y_6320_);
    return v_res_6327_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17(
    mut v_00_u03b2_6328_: *mut crate::leanh::LeanObject,
    mut v_m_6329_: *mut crate::leanh::LeanObject,
    mut v_a_6330_: *mut crate::leanh::LeanObject,
    mut v_b_6331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6332_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17___redArg(v_m_6329_, v_a_6330_, v_b_6331_);
    return v___x_6332_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_6333_: *mut crate::leanh::LeanObject,
    mut v_x_6334_: *mut crate::leanh::LeanObject,
    mut v_x_6335_: usize,
    mut v_x_6336_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6337_: u8 = 0;
    v___x_6337_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___redArg(v_x_6334_, v_x_6335_, v_x_6336_);
    return v___x_6337_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_6338_: *mut crate::leanh::LeanObject,
    mut v_x_6339_: *mut crate::leanh::LeanObject,
    mut v_x_6340_: *mut crate::leanh::LeanObject,
    mut v_x_6341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40440__boxed_6342_: usize = 0;
    let mut v_res_6343_: u8 = 0;
    let mut v_r_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40440__boxed_6342_ = crate::leanh::lean_unbox_usize(v_x_6340_);
    crate::leanh::lean_dec(v_x_6340_);
    v_res_6343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_6338_, v_x_6339_, v_x_40440__boxed_6342_, v_x_6341_);
    crate::leanh::lean_dec_ref(v_x_6341_);
    crate::leanh::lean_dec_ref(v_x_6339_);
    v_r_6344_ = crate::leanh::lean_box((v_res_6343_) as usize);
    return v_r_6344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(
    mut v_00_u03b2_6345_: *mut crate::leanh::LeanObject,
    mut v_a_6346_: *mut crate::leanh::LeanObject,
    mut v_x_6347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___redArg(v_a_6346_, v_x_6347_);
    return v___x_6348_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14___boxed(
    mut v_00_u03b2_6349_: *mut crate::leanh::LeanObject,
    mut v_a_6350_: *mut crate::leanh::LeanObject,
    mut v_x_6351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__11_spec__14(v_00_u03b2_6349_, v_a_6350_, v_x_6351_);
    crate::leanh::lean_dec(v_x_6351_);
    crate::leanh::lean_dec_ref(v_a_6350_);
    return v_res_6352_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(
    mut v_00_u03b2_6353_: *mut crate::leanh::LeanObject,
    mut v_a_6354_: *mut crate::leanh::LeanObject,
    mut v_x_6355_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6356_: u8 = 0;
    v___x_6356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___redArg(v_a_6354_, v_x_6355_);
    return v___x_6356_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24___boxed(
    mut v_00_u03b2_6357_: *mut crate::leanh::LeanObject,
    mut v_a_6358_: *mut crate::leanh::LeanObject,
    mut v_x_6359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6360_: u8 = 0;
    let mut v_r_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__24(v_00_u03b2_6357_, v_a_6358_, v_x_6359_);
    crate::leanh::lean_dec(v_x_6359_);
    crate::leanh::lean_dec_ref(v_a_6358_);
    v_r_6361_ = crate::leanh::lean_box((v_res_6360_) as usize);
    return v_r_6361_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25(
    mut v_00_u03b2_6362_: *mut crate::leanh::LeanObject,
    mut v_data_6363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25___redArg(v_data_6363_);
    return v___x_6364_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26(
    mut v_00_u03b2_6365_: *mut crate::leanh::LeanObject,
    mut v_a_6366_: *mut crate::leanh::LeanObject,
    mut v_b_6367_: *mut crate::leanh::LeanObject,
    mut v_x_6368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__26___redArg(v_a_6366_, v_b_6367_, v_x_6368_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_6370_: *mut crate::leanh::LeanObject,
    mut v_keys_6371_: *mut crate::leanh::LeanObject,
    mut v_vals_6372_: *mut crate::leanh::LeanObject,
    mut v_heq_6373_: *mut crate::leanh::LeanObject,
    mut v_i_6374_: *mut crate::leanh::LeanObject,
    mut v_k_6375_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6376_: u8 = 0;
    v___x_6376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_6371_, v_i_6374_, v_k_6375_);
    return v___x_6376_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_6377_: *mut crate::leanh::LeanObject,
    mut v_keys_6378_: *mut crate::leanh::LeanObject,
    mut v_vals_6379_: *mut crate::leanh::LeanObject,
    mut v_heq_6380_: *mut crate::leanh::LeanObject,
    mut v_i_6381_: *mut crate::leanh::LeanObject,
    mut v_k_6382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6383_: u8 = 0;
    let mut v_r_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_6377_, v_keys_6378_, v_vals_6379_, v_heq_6380_, v_i_6381_, v_k_6382_);
    crate::leanh::lean_dec_ref(v_k_6382_);
    crate::leanh::lean_dec_ref(v_vals_6379_);
    crate::leanh::lean_dec_ref(v_keys_6378_);
    v_r_6384_ = crate::leanh::lean_box((v_res_6383_) as usize);
    return v_r_6384_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27(
    mut v_00_u03b2_6385_: *mut crate::leanh::LeanObject,
    mut v_i_6386_: *mut crate::leanh::LeanObject,
    mut v_source_6387_: *mut crate::leanh::LeanObject,
    mut v_target_6388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6389_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27___redArg(v_i_6386_, v_source_6387_, v_target_6388_);
    return v___x_6389_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28(
    mut v_00_u03b2_6390_: *mut crate::leanh::LeanObject,
    mut v_x_6391_: *mut crate::leanh::LeanObject,
    mut v_x_6392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6393_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_expandCoe_spec__1_spec__4_spec__17_spec__25_spec__27_spec__28___redArg(v_x_6391_, v_x_6392_);
    return v___x_6393_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(
    mut v_name_6394_: *mut crate::leanh::LeanObject,
    mut v_decl_6395_: *mut crate::leanh::LeanObject,
    mut v_ref_6396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: u8 = 0;
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6407_: u8 = 0;
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6412_: u8 = 0;
    let mut v_unused_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6417_: u8 = 0;
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_6398_ = crate::leanh::lean_ctor_get(v_decl_6395_, 0);
                v_descr_6399_ = crate::leanh::lean_ctor_get(v_decl_6395_, 1);
                v_deprecation_x3f_6400_ = crate::leanh::lean_ctor_get(v_decl_6395_, 2);
                v___x_6401_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_6402_ = (crate::leanh::lean_unbox(v_defValue_6398_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_6401_, 0 as u32, v___x_6402_);
                crate::leanh::lean_inc(v_deprecation_x3f_6400_);
                crate::leanh::lean_inc_ref(v_descr_6399_);
                crate::leanh::lean_inc_n(v_name_6394_, 2);
                v___x_6403_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6403_, 0, v_name_6394_);
                crate::leanh::lean_ctor_set(v___x_6403_, 1, v_ref_6396_);
                crate::leanh::lean_ctor_set(v___x_6403_, 2, v___x_6401_);
                crate::leanh::lean_ctor_set(v___x_6403_, 3, v_descr_6399_);
                crate::leanh::lean_ctor_set(v___x_6403_, 4, v_deprecation_x3f_6400_);
                v___x_6404_ = lean_register_option(v_name_6394_, v___x_6403_);
                if crate::leanh::lean_obj_tag(v___x_6404_) == 0 {
                    v_isSharedCheck_6412_ = (!crate::leanh::lean_is_exclusive(v___x_6404_)) as u8;
                    if v_isSharedCheck_6412_ == 0 {
                        v_unused_6413_ = crate::leanh::lean_ctor_get(v___x_6404_, 0);
                        crate::leanh::lean_dec(v_unused_6413_);
                        v___x_6406_ = v___x_6404_;
                        v_isShared_6407_ = v_isSharedCheck_6412_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6404_);
                        v___x_6406_ = crate::leanh::lean_box(0);
                        v_isShared_6407_ = v_isSharedCheck_6412_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_6394_);
                    v_a_6414_ = crate::leanh::lean_ctor_get(v___x_6404_, 0);
                    v_isSharedCheck_6421_ = (!crate::leanh::lean_is_exclusive(v___x_6404_)) as u8;
                    if v_isSharedCheck_6421_ == 0 {
                        v___x_6416_ = v___x_6404_;
                        v_isShared_6417_ = v_isSharedCheck_6421_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6414_);
                        crate::leanh::lean_dec(v___x_6404_);
                        v___x_6416_ = crate::leanh::lean_box(0);
                        v_isShared_6417_ = v_isSharedCheck_6421_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_6398_);
                v___x_6408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6408_, 0, v_name_6394_);
                crate::leanh::lean_ctor_set(v___x_6408_, 1, v_defValue_6398_);
                if v_isShared_6407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6406_, 0, v___x_6408_);
                    v___x_6410_ = v___x_6406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 0, v___x_6408_);
                    v___x_6410_ = v_reuseFailAlloc_6411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6410_;
            }
            3 => {
                if v_isShared_6417_ == 0 {
                    v___x_6419_ = v___x_6416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
                    v___x_6419_ = v_reuseFailAlloc_6420_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_6422_: *mut crate::leanh::LeanObject,
    mut v_decl_6423_: *mut crate::leanh::LeanObject,
    mut v_ref_6424_: *mut crate::leanh::LeanObject,
    mut v_a_6425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6426_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v_name_6422_, v_decl_6423_, v_ref_6424_);
    crate::leanh::lean_dec_ref(v_decl_6423_);
    return v_res_6426_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6441_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_;
    v___x_6442_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_;
    v___x_6443_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_;
    v___x_6444_ = l_Lean_Option_register___at___00__private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4__spec__0(v___x_6441_, v___x_6442_, v___x_6443_);
    return v___x_6444_;
}
pub unsafe fn l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4____boxed(
    mut v_a_6445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6446_ = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
    return v_res_6446_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(
    mut v_msg_6447_: *mut crate::leanh::LeanObject,
    mut v___y_6448_: *mut crate::leanh::LeanObject,
    mut v___y_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6458_: u8 = 0;
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6453_ = crate::leanh::lean_ctor_get(v___y_6450_, 5);
                v___x_6454_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_expandCoe_spec__0_spec__0_spec__2_spec__5(v_msg_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_);
                v_a_6455_ = crate::leanh::lean_ctor_get(v___x_6454_, 0);
                v_isSharedCheck_6463_ = (!crate::leanh::lean_is_exclusive(v___x_6454_)) as u8;
                if v_isSharedCheck_6463_ == 0 {
                    v___x_6457_ = v___x_6454_;
                    v_isShared_6458_ = v_isSharedCheck_6463_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6455_);
                    crate::leanh::lean_dec(v___x_6454_);
                    v___x_6457_ = crate::leanh::lean_box(0);
                    v_isShared_6458_ = v_isSharedCheck_6463_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_6453_);
                v___x_6459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6459_, 0, v_ref_6453_);
                crate::leanh::lean_ctor_set(v___x_6459_, 1, v_a_6455_);
                if v_isShared_6458_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6457_, 1);
                    crate::leanh::lean_ctor_set(v___x_6457_, 0, v___x_6459_);
                    v___x_6461_ = v___x_6457_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6459_);
                    v___x_6461_ = v_reuseFailAlloc_6462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg___boxed(
    mut v_msg_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
    mut v___y_6469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6470_ =
        l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(
            v_msg_6464_,
            v___y_6465_,
            v___y_6466_,
            v___y_6467_,
            v___y_6468_,
        );
    crate::leanh::lean_dec(v___y_6468_);
    crate::leanh::lean_dec_ref(v___y_6467_);
    crate::leanh::lean_dec(v___y_6466_);
    crate::leanh::lean_dec_ref(v___y_6465_);
    return v_res_6470_;
}
pub unsafe fn _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6478_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__3;
    v___x_6479_ = l_Lean_stringToMessageData(v___x_6478_);
    return v___x_6479_;
}
pub unsafe fn _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6481_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__5;
    v___x_6482_ = l_Lean_stringToMessageData(v___x_6481_);
    return v___x_6482_;
}
pub unsafe fn _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6484_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__7;
    v___x_6485_ = l_Lean_stringToMessageData(v___x_6484_);
    return v___x_6485_;
}
pub unsafe fn l_Lean_Meta_coerceSimpleRecordingNames_x3f(
    mut v_expr_6486_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6487_: *mut crate::leanh::LeanObject,
    mut v_a_6488_: *mut crate::leanh::LeanObject,
    mut v_a_6489_: *mut crate::leanh::LeanObject,
    mut v_a_6490_: *mut crate::leanh::LeanObject,
    mut v_a_6491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6515_: u8 = 0;
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6523_: u8 = 0;
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: u8 = 0;
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6553_: u8 = 0;
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6570_: u8 = 0;
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6574_: u8 = 0;
    let mut v_reuseFailAlloc_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v_unused_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6582_: u8 = 0;
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6586_: u8 = 0;
    let mut v_a_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6590_: u8 = 0;
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6594_: u8 = 0;
    let mut v_isSharedCheck_6595_: u8 = 0;
    let mut v_a_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut v_isSharedCheck_6604_: u8 = 0;
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut v_a_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6613_: u8 = 0;
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6617_: u8 = 0;
    let mut v_a_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6625_: u8 = 0;
    let mut v_a_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6629_: u8 = 0;
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6633_: u8 = 0;
    let mut v_a_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6491_);
                crate::leanh::lean_inc_ref(v_a_6490_);
                crate::leanh::lean_inc(v_a_6489_);
                crate::leanh::lean_inc_ref(v_a_6488_);
                crate::leanh::lean_inc_ref(v_expr_6486_);
                v___x_6493_ =
                    lean_infer_type(v_expr_6486_, v_a_6488_, v_a_6489_, v_a_6490_, v_a_6491_);
                if crate::leanh::lean_obj_tag(v___x_6493_) == 0 {
                    v_a_6494_ = crate::leanh::lean_ctor_get(v___x_6493_, 0);
                    crate::leanh::lean_inc_n(v_a_6494_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6493_, 1);
                    v___x_6495_ =
                        l_Lean_Meta_getLevel(v_a_6494_, v_a_6488_, v_a_6489_, v_a_6490_, v_a_6491_);
                    if crate::leanh::lean_obj_tag(v___x_6495_) == 0 {
                        v_a_6496_ = crate::leanh::lean_ctor_get(v___x_6495_, 0);
                        crate::leanh::lean_inc(v_a_6496_);
                        crate::leanh::lean_dec_ref_known(v___x_6495_, 1);
                        crate::leanh::lean_inc_ref(v_expectedType_6487_);
                        v___x_6497_ = l_Lean_Meta_getLevel(
                            v_expectedType_6487_,
                            v_a_6488_,
                            v_a_6489_,
                            v_a_6490_,
                            v_a_6491_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6497_) == 0 {
                            v_a_6498_ = crate::leanh::lean_ctor_get(v___x_6497_, 0);
                            crate::leanh::lean_inc(v_a_6498_);
                            crate::leanh::lean_dec_ref_known(v___x_6497_, 1);
                            v___x_6499_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1;
                            v___x_6500_ = crate::leanh::lean_box(0);
                            v___x_6501_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6501_, 0, v_a_6498_);
                            crate::leanh::lean_ctor_set(v___x_6501_, 1, v___x_6500_);
                            v___x_6502_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6502_, 0, v_a_6496_);
                            crate::leanh::lean_ctor_set(v___x_6502_, 1, v___x_6501_);
                            crate::leanh::lean_inc_ref(v___x_6502_);
                            v___x_6503_ = l_Lean_mkConst(v___x_6499_, v___x_6502_);
                            v___x_6504_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_6505_ = lean_mk_empty_array_with_capacity(v___x_6504_);
                            crate::leanh::lean_inc(v_a_6494_);
                            v___x_6506_ = lean_array_push(v___x_6505_, v_a_6494_);
                            crate::leanh::lean_inc_ref(v_expr_6486_);
                            v___x_6507_ = lean_array_push(v___x_6506_, v_expr_6486_);
                            crate::leanh::lean_inc_ref(v_expectedType_6487_);
                            v___x_6508_ = lean_array_push(v___x_6507_, v_expectedType_6487_);
                            v___x_6509_ = l_Lean_mkAppN(v___x_6503_, v___x_6508_);
                            crate::leanh::lean_dec_ref(v___x_6508_);
                            v___x_6510_ = crate::leanh::lean_box(0);
                            v___x_6511_ = l_Lean_Meta_trySynthInstance(
                                v___x_6509_,
                                v___x_6510_,
                                v_a_6488_,
                                v_a_6489_,
                                v_a_6490_,
                                v_a_6491_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6511_) == 0 {
                                v_a_6512_ = crate::leanh::lean_ctor_get(v___x_6511_, 0);
                                v_isSharedCheck_6609_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6511_)) as u8;
                                if v_isSharedCheck_6609_ == 0 {
                                    v___x_6514_ = v___x_6511_;
                                    v_isShared_6515_ = v_isSharedCheck_6609_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6512_);
                                    crate::leanh::lean_dec(v___x_6511_);
                                    v___x_6514_ = crate::leanh::lean_box(0);
                                    v_isShared_6515_ = v_isSharedCheck_6609_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_6502_, 2);
                                crate::leanh::lean_dec(v_a_6494_);
                                crate::leanh::lean_dec_ref(v_expectedType_6487_);
                                crate::leanh::lean_dec_ref(v_expr_6486_);
                                v_a_6610_ = crate::leanh::lean_ctor_get(v___x_6511_, 0);
                                v_isSharedCheck_6617_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6511_)) as u8;
                                if v_isSharedCheck_6617_ == 0 {
                                    v___x_6612_ = v___x_6511_;
                                    v_isShared_6613_ = v_isSharedCheck_6617_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6610_);
                                    crate::leanh::lean_dec(v___x_6511_);
                                    v___x_6612_ = crate::leanh::lean_box(0);
                                    v_isShared_6613_ = v_isSharedCheck_6617_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6496_);
                            crate::leanh::lean_dec(v_a_6494_);
                            crate::leanh::lean_dec_ref(v_expectedType_6487_);
                            crate::leanh::lean_dec_ref(v_expr_6486_);
                            v_a_6618_ = crate::leanh::lean_ctor_get(v___x_6497_, 0);
                            v_isSharedCheck_6625_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6497_)) as u8;
                            if v_isSharedCheck_6625_ == 0 {
                                v___x_6620_ = v___x_6497_;
                                v_isShared_6621_ = v_isSharedCheck_6625_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6618_);
                                crate::leanh::lean_dec(v___x_6497_);
                                v___x_6620_ = crate::leanh::lean_box(0);
                                v_isShared_6621_ = v_isSharedCheck_6625_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6494_);
                        crate::leanh::lean_dec_ref(v_expectedType_6487_);
                        crate::leanh::lean_dec_ref(v_expr_6486_);
                        v_a_6626_ = crate::leanh::lean_ctor_get(v___x_6495_, 0);
                        v_isSharedCheck_6633_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6495_)) as u8;
                        if v_isSharedCheck_6633_ == 0 {
                            v___x_6628_ = v___x_6495_;
                            v_isShared_6629_ = v_isSharedCheck_6633_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6626_);
                            crate::leanh::lean_dec(v___x_6495_);
                            v___x_6628_ = crate::leanh::lean_box(0);
                            v_isShared_6629_ = v_isSharedCheck_6633_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_expectedType_6487_);
                    crate::leanh::lean_dec_ref(v_expr_6486_);
                    v_a_6634_ = crate::leanh::lean_ctor_get(v___x_6493_, 0);
                    v_isSharedCheck_6641_ = (!crate::leanh::lean_is_exclusive(v___x_6493_)) as u8;
                    if v_isSharedCheck_6641_ == 0 {
                        v___x_6636_ = v___x_6493_;
                        v_isShared_6637_ = v_isSharedCheck_6641_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6634_);
                        crate::leanh::lean_dec(v___x_6493_);
                        v___x_6636_ = crate::leanh::lean_box(0);
                        v_isShared_6637_ = v_isSharedCheck_6641_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_6512_) {
                0 => {
                    crate::leanh::lean_dec_ref_known(v___x_6502_, 2);
                    crate::leanh::lean_dec(v_a_6494_);
                    crate::leanh::lean_dec_ref(v_expectedType_6487_);
                    crate::leanh::lean_dec_ref(v_expr_6486_);
                    v___x_6516_ = crate::leanh::lean_box(0);
                    if v_isShared_6515_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6514_, 0, v___x_6516_);
                        v___x_6518_ = v___x_6514_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6519_, 0, v___x_6516_);
                        v___x_6518_ = v_reuseFailAlloc_6519_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6514_);
                    v_a_6520_ = crate::leanh::lean_ctor_get(v_a_6512_, 0);
                    v_isSharedCheck_6604_ = (!crate::leanh::lean_is_exclusive(v_a_6512_)) as u8;
                    if v_isSharedCheck_6604_ == 0 {
                        v___x_6522_ = v_a_6512_;
                        v_isShared_6523_ = v_isSharedCheck_6604_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6520_);
                        crate::leanh::lean_dec(v_a_6512_);
                        v___x_6522_ = crate::leanh::lean_box(0);
                        v_isShared_6523_ = v_isSharedCheck_6604_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref_known(v___x_6502_, 2);
                    crate::leanh::lean_dec(v_a_6494_);
                    crate::leanh::lean_dec_ref(v_expectedType_6487_);
                    crate::leanh::lean_dec_ref(v_expr_6486_);
                    v___x_6605_ = crate::leanh::lean_box(2);
                    if v_isShared_6515_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6514_, 0, v___x_6605_);
                        v___x_6607_ = v___x_6514_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_6608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6608_, 0, v___x_6605_);
                        v___x_6607_ = v_reuseFailAlloc_6608_;
                        state = 18;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_6518_;
            }
            3 => {
                v___x_6524_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__2;
                v___x_6525_ = l_Lean_mkConst(v___x_6524_, v___x_6502_);
                v___x_6526_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_6527_ = lean_mk_empty_array_with_capacity(v___x_6526_);
                v___x_6528_ = lean_array_push(v___x_6527_, v_a_6494_);
                crate::leanh::lean_inc_ref(v_expr_6486_);
                v___x_6529_ = lean_array_push(v___x_6528_, v_expr_6486_);
                crate::leanh::lean_inc_ref(v_expectedType_6487_);
                v___x_6530_ = lean_array_push(v___x_6529_, v_expectedType_6487_);
                v___x_6531_ = lean_array_push(v___x_6530_, v_a_6520_);
                v___x_6532_ = l_Lean_mkAppN(v___x_6525_, v___x_6531_);
                crate::leanh::lean_dec_ref(v___x_6531_);
                v___x_6533_ =
                    l_Lean_Meta_expandCoe(v___x_6532_, v_a_6488_, v_a_6489_, v_a_6490_, v_a_6491_);
                if crate::leanh::lean_obj_tag(v___x_6533_) == 0 {
                    v_a_6534_ = crate::leanh::lean_ctor_get(v___x_6533_, 0);
                    v_isSharedCheck_6595_ = (!crate::leanh::lean_is_exclusive(v___x_6533_)) as u8;
                    if v_isSharedCheck_6595_ == 0 {
                        v___x_6536_ = v___x_6533_;
                        v_isShared_6537_ = v_isSharedCheck_6595_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6534_);
                        crate::leanh::lean_dec(v___x_6533_);
                        v___x_6536_ = crate::leanh::lean_box(0);
                        v_isShared_6537_ = v_isSharedCheck_6595_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6522_);
                    crate::leanh::lean_dec_ref(v_expectedType_6487_);
                    crate::leanh::lean_dec_ref(v_expr_6486_);
                    v_a_6596_ = crate::leanh::lean_ctor_get(v___x_6533_, 0);
                    v_isSharedCheck_6603_ = (!crate::leanh::lean_is_exclusive(v___x_6533_)) as u8;
                    if v_isSharedCheck_6603_ == 0 {
                        v___x_6598_ = v___x_6533_;
                        v_isShared_6599_ = v_isSharedCheck_6603_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6596_);
                        crate::leanh::lean_dec(v___x_6533_);
                        v___x_6598_ = crate::leanh::lean_box(0);
                        v_isShared_6599_ = v_isSharedCheck_6603_;
                        state = 16;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_6545_ = crate::leanh::lean_ctor_get(v_a_6534_, 0);
                crate::leanh::lean_inc(v_a_6491_);
                crate::leanh::lean_inc_ref(v_a_6490_);
                crate::leanh::lean_inc(v_a_6489_);
                crate::leanh::lean_inc_ref(v_a_6488_);
                crate::leanh::lean_inc(v_fst_6545_);
                v___x_6546_ =
                    lean_infer_type(v_fst_6545_, v_a_6488_, v_a_6489_, v_a_6490_, v_a_6491_);
                if crate::leanh::lean_obj_tag(v___x_6546_) == 0 {
                    v_a_6547_ = crate::leanh::lean_ctor_get(v___x_6546_, 0);
                    crate::leanh::lean_inc(v_a_6547_);
                    crate::leanh::lean_dec_ref_known(v___x_6546_, 1);
                    crate::leanh::lean_inc_ref(v_expectedType_6487_);
                    v___x_6548_ = l_Lean_Meta_isExprDefEq(
                        v_a_6547_,
                        v_expectedType_6487_,
                        v_a_6488_,
                        v_a_6489_,
                        v_a_6490_,
                        v_a_6491_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6548_) == 0 {
                        v_a_6549_ = crate::leanh::lean_ctor_get(v___x_6548_, 0);
                        crate::leanh::lean_inc(v_a_6549_);
                        crate::leanh::lean_dec_ref_known(v___x_6548_, 1);
                        v___x_6550_ = (crate::leanh::lean_unbox(v_a_6549_) as u8);
                        crate::leanh::lean_dec(v_a_6549_);
                        if v___x_6550_ == 0 {
                            crate::leanh::lean_inc(v_fst_6545_);
                            crate::leanh::lean_del_object(v___x_6536_);
                            crate::leanh::lean_del_object(v___x_6522_);
                            v_isSharedCheck_6576_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6534_)) as u8;
                            if v_isSharedCheck_6576_ == 0 {
                                v_unused_6577_ = crate::leanh::lean_ctor_get(v_a_6534_, 1);
                                crate::leanh::lean_dec(v_unused_6577_);
                                v_unused_6578_ = crate::leanh::lean_ctor_get(v_a_6534_, 0);
                                crate::leanh::lean_dec(v_unused_6578_);
                                v___x_6552_ = v_a_6534_;
                                v_isShared_6553_ = v_isSharedCheck_6576_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6534_);
                                v___x_6552_ = crate::leanh::lean_box(0);
                                v_isShared_6553_ = v_isSharedCheck_6576_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_expectedType_6487_);
                            crate::leanh::lean_dec_ref(v_expr_6486_);
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6536_);
                        crate::leanh::lean_dec(v_a_6534_);
                        crate::leanh::lean_del_object(v___x_6522_);
                        crate::leanh::lean_dec_ref(v_expectedType_6487_);
                        crate::leanh::lean_dec_ref(v_expr_6486_);
                        v_a_6579_ = crate::leanh::lean_ctor_get(v___x_6548_, 0);
                        v_isSharedCheck_6586_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6548_)) as u8;
                        if v_isSharedCheck_6586_ == 0 {
                            v___x_6581_ = v___x_6548_;
                            v_isShared_6582_ = v_isSharedCheck_6586_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6579_);
                            crate::leanh::lean_dec(v___x_6548_);
                            v___x_6581_ = crate::leanh::lean_box(0);
                            v_isShared_6582_ = v_isSharedCheck_6586_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6536_);
                    crate::leanh::lean_dec(v_a_6534_);
                    crate::leanh::lean_del_object(v___x_6522_);
                    crate::leanh::lean_dec_ref(v_expectedType_6487_);
                    crate::leanh::lean_dec_ref(v_expr_6486_);
                    v_a_6587_ = crate::leanh::lean_ctor_get(v___x_6546_, 0);
                    v_isSharedCheck_6594_ = (!crate::leanh::lean_is_exclusive(v___x_6546_)) as u8;
                    if v_isSharedCheck_6594_ == 0 {
                        v___x_6589_ = v___x_6546_;
                        v_isShared_6590_ = v_isSharedCheck_6594_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6587_);
                        crate::leanh::lean_dec(v___x_6546_);
                        v___x_6589_ = crate::leanh::lean_box(0);
                        v_isShared_6590_ = v_isSharedCheck_6594_;
                        state = 14;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6522_, 0, v_a_6534_);
                    v___x_6540_ = v___x_6522_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6544_, 0, v_a_6534_);
                    v___x_6540_ = v_reuseFailAlloc_6544_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6537_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6536_, 0, v___x_6540_);
                    v___x_6542_ = v___x_6536_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6543_, 0, v___x_6540_);
                    v___x_6542_ = v_reuseFailAlloc_6543_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6542_;
            }
            8 => {
                v___x_6554_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4_once
                    ),
                    _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__4,
                );
                v___x_6555_ = l_Lean_indentExpr(v_expr_6486_);
                if v_isShared_6553_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6552_, 7);
                    crate::leanh::lean_ctor_set(v___x_6552_, 1, v___x_6555_);
                    crate::leanh::lean_ctor_set(v___x_6552_, 0, v___x_6554_);
                    v___x_6557_ = v___x_6552_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6554_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 1, v___x_6555_);
                    v___x_6557_ = v_reuseFailAlloc_6575_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6558_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6_once
                    ),
                    _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__6,
                );
                v___x_6559_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6559_, 0, v___x_6557_);
                crate::leanh::lean_ctor_set(v___x_6559_, 1, v___x_6558_);
                v___x_6560_ = l_Lean_indentExpr(v_expectedType_6487_);
                v___x_6561_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6561_, 0, v___x_6559_);
                crate::leanh::lean_ctor_set(v___x_6561_, 1, v___x_6560_);
                v___x_6562_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8_once
                    ),
                    _init_l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__8,
                );
                v___x_6563_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6563_, 0, v___x_6561_);
                crate::leanh::lean_ctor_set(v___x_6563_, 1, v___x_6562_);
                v___x_6564_ = l_Lean_indentExpr(v_fst_6545_);
                v___x_6565_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6565_, 0, v___x_6563_);
                crate::leanh::lean_ctor_set(v___x_6565_, 1, v___x_6564_);
                v___x_6566_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_6565_, v_a_6488_, v_a_6489_, v_a_6490_, v_a_6491_);
                v_a_6567_ = crate::leanh::lean_ctor_get(v___x_6566_, 0);
                v_isSharedCheck_6574_ = (!crate::leanh::lean_is_exclusive(v___x_6566_)) as u8;
                if v_isSharedCheck_6574_ == 0 {
                    v___x_6569_ = v___x_6566_;
                    v_isShared_6570_ = v_isSharedCheck_6574_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6567_);
                    crate::leanh::lean_dec(v___x_6566_);
                    v___x_6569_ = crate::leanh::lean_box(0);
                    v_isShared_6570_ = v_isSharedCheck_6574_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6570_ == 0 {
                    v___x_6572_ = v___x_6569_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6573_, 0, v_a_6567_);
                    v___x_6572_ = v_reuseFailAlloc_6573_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6572_;
            }
            12 => {
                if v_isShared_6582_ == 0 {
                    v___x_6584_ = v___x_6581_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6585_, 0, v_a_6579_);
                    v___x_6584_ = v_reuseFailAlloc_6585_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6584_;
            }
            14 => {
                if v_isShared_6590_ == 0 {
                    v___x_6592_ = v___x_6589_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
                    v___x_6592_ = v_reuseFailAlloc_6593_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6592_;
            }
            16 => {
                if v_isShared_6599_ == 0 {
                    v___x_6601_ = v___x_6598_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6602_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6601_;
            }
            18 => {
                return v___x_6607_;
            }
            19 => {
                if v_isShared_6613_ == 0 {
                    v___x_6615_ = v___x_6612_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6616_, 0, v_a_6610_);
                    v___x_6615_ = v_reuseFailAlloc_6616_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6615_;
            }
            21 => {
                if v_isShared_6621_ == 0 {
                    v___x_6623_ = v___x_6620_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 0, v_a_6618_);
                    v___x_6623_ = v_reuseFailAlloc_6624_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6623_;
            }
            23 => {
                if v_isShared_6629_ == 0 {
                    v___x_6631_ = v___x_6628_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_a_6626_);
                    v___x_6631_ = v_reuseFailAlloc_6632_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6631_;
            }
            25 => {
                if v_isShared_6637_ == 0 {
                    v___x_6639_ = v___x_6636_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
                    v___x_6639_ = v_reuseFailAlloc_6640_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerceSimpleRecordingNames_x3f___boxed(
    mut v_expr_6642_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6643_: *mut crate::leanh::LeanObject,
    mut v_a_6644_: *mut crate::leanh::LeanObject,
    mut v_a_6645_: *mut crate::leanh::LeanObject,
    mut v_a_6646_: *mut crate::leanh::LeanObject,
    mut v_a_6647_: *mut crate::leanh::LeanObject,
    mut v_a_6648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6649_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(
        v_expr_6642_,
        v_expectedType_6643_,
        v_a_6644_,
        v_a_6645_,
        v_a_6646_,
        v_a_6647_,
    );
    crate::leanh::lean_dec(v_a_6647_);
    crate::leanh::lean_dec_ref(v_a_6646_);
    crate::leanh::lean_dec(v_a_6645_);
    crate::leanh::lean_dec_ref(v_a_6644_);
    return v_res_6649_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(
    mut v_00_u03b1_6650_: *mut crate::leanh::LeanObject,
    mut v_msg_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6657_ =
        l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(
            v_msg_6651_,
            v___y_6652_,
            v___y_6653_,
            v___y_6654_,
            v___y_6655_,
        );
    return v___x_6657_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___boxed(
    mut v_00_u03b1_6658_: *mut crate::leanh::LeanObject,
    mut v_msg_6659_: *mut crate::leanh::LeanObject,
    mut v___y_6660_: *mut crate::leanh::LeanObject,
    mut v___y_6661_: *mut crate::leanh::LeanObject,
    mut v___y_6662_: *mut crate::leanh::LeanObject,
    mut v___y_6663_: *mut crate::leanh::LeanObject,
    mut v___y_6664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6665_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0(
        v_00_u03b1_6658_,
        v_msg_6659_,
        v___y_6660_,
        v___y_6661_,
        v___y_6662_,
        v___y_6663_,
    );
    crate::leanh::lean_dec(v___y_6663_);
    crate::leanh::lean_dec_ref(v___y_6662_);
    crate::leanh::lean_dec(v___y_6661_);
    crate::leanh::lean_dec_ref(v___y_6660_);
    return v_res_6665_;
}
pub unsafe fn l_Lean_Meta_coerceSimple_x3f(
    mut v_expr_6666_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6667_: *mut crate::leanh::LeanObject,
    mut v_a_6668_: *mut crate::leanh::LeanObject,
    mut v_a_6669_: *mut crate::leanh::LeanObject,
    mut v_a_6670_: *mut crate::leanh::LeanObject,
    mut v_a_6671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6677_: u8 = 0;
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6685_: u8 = 0;
    let mut v_fst_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6693_: u8 = 0;
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6698_: u8 = 0;
    let mut v_a_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6702_: u8 = 0;
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6673_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(
                    v_expr_6666_,
                    v_expectedType_6667_,
                    v_a_6668_,
                    v_a_6669_,
                    v_a_6670_,
                    v_a_6671_,
                );
                if crate::leanh::lean_obj_tag(v___x_6673_) == 0 {
                    v_a_6674_ = crate::leanh::lean_ctor_get(v___x_6673_, 0);
                    v_isSharedCheck_6698_ = (!crate::leanh::lean_is_exclusive(v___x_6673_)) as u8;
                    if v_isSharedCheck_6698_ == 0 {
                        v___x_6676_ = v___x_6673_;
                        v_isShared_6677_ = v_isSharedCheck_6698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6674_);
                        crate::leanh::lean_dec(v___x_6673_);
                        v___x_6676_ = crate::leanh::lean_box(0);
                        v_isShared_6677_ = v_isSharedCheck_6698_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6699_ = crate::leanh::lean_ctor_get(v___x_6673_, 0);
                    v_isSharedCheck_6706_ = (!crate::leanh::lean_is_exclusive(v___x_6673_)) as u8;
                    if v_isSharedCheck_6706_ == 0 {
                        v___x_6701_ = v___x_6673_;
                        v_isShared_6702_ = v_isSharedCheck_6706_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6699_);
                        crate::leanh::lean_dec(v___x_6673_);
                        v___x_6701_ = crate::leanh::lean_box(0);
                        v_isShared_6702_ = v_isSharedCheck_6706_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_6674_) {
                0 => {
                    v___x_6678_ = crate::leanh::lean_box(0);
                    if v_isShared_6677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6676_, 0, v___x_6678_);
                        v___x_6680_ = v___x_6676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6681_, 0, v___x_6678_);
                        v___x_6680_ = v_reuseFailAlloc_6681_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_a_6682_ = crate::leanh::lean_ctor_get(v_a_6674_, 0);
                    v_isSharedCheck_6693_ = (!crate::leanh::lean_is_exclusive(v_a_6674_)) as u8;
                    if v_isSharedCheck_6693_ == 0 {
                        v___x_6684_ = v_a_6674_;
                        v_isShared_6685_ = v_isSharedCheck_6693_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6682_);
                        crate::leanh::lean_dec(v_a_6674_);
                        v___x_6684_ = crate::leanh::lean_box(0);
                        v_isShared_6685_ = v_isSharedCheck_6693_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_6694_ = crate::leanh::lean_box(2);
                    if v_isShared_6677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6676_, 0, v___x_6694_);
                        v___x_6696_ = v___x_6676_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6697_, 0, v___x_6694_);
                        v___x_6696_ = v_reuseFailAlloc_6697_;
                        state = 6;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_6680_;
            }
            3 => {
                v_fst_6686_ = crate::leanh::lean_ctor_get(v_a_6682_, 0);
                crate::leanh::lean_inc(v_fst_6686_);
                crate::leanh::lean_dec(v_a_6682_);
                if v_isShared_6685_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6684_, 0, v_fst_6686_);
                    v___x_6688_ = v___x_6684_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 0, v_fst_6686_);
                    v___x_6688_ = v_reuseFailAlloc_6692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6676_, 0, v___x_6688_);
                    v___x_6690_ = v___x_6676_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6691_, 0, v___x_6688_);
                    v___x_6690_ = v_reuseFailAlloc_6691_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6690_;
            }
            6 => {
                return v___x_6696_;
            }
            7 => {
                if v_isShared_6702_ == 0 {
                    v___x_6704_ = v___x_6701_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6705_, 0, v_a_6699_);
                    v___x_6704_ = v_reuseFailAlloc_6705_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerceSimple_x3f___boxed(
    mut v_expr_6707_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6708_: *mut crate::leanh::LeanObject,
    mut v_a_6709_: *mut crate::leanh::LeanObject,
    mut v_a_6710_: *mut crate::leanh::LeanObject,
    mut v_a_6711_: *mut crate::leanh::LeanObject,
    mut v_a_6712_: *mut crate::leanh::LeanObject,
    mut v_a_6713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6714_ = l_Lean_Meta_coerceSimple_x3f(
        v_expr_6707_,
        v_expectedType_6708_,
        v_a_6709_,
        v_a_6710_,
        v_a_6711_,
        v_a_6712_,
    );
    crate::leanh::lean_dec(v_a_6712_);
    crate::leanh::lean_dec_ref(v_a_6711_);
    crate::leanh::lean_dec(v_a_6710_);
    crate::leanh::lean_dec_ref(v_a_6709_);
    return v_res_6714_;
}
pub unsafe fn _init_l_Lean_Meta_coerceToFunction_x3f___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6722_ = l_Lean_Meta_coerceToFunction_x3f___closed__3;
    v___x_6723_ = l_Lean_stringToMessageData(v___x_6722_);
    return v___x_6723_;
}
pub unsafe fn _init_l_Lean_Meta_coerceToFunction_x3f___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6725_ = l_Lean_Meta_coerceToFunction_x3f___closed__5;
    v___x_6726_ = l_Lean_stringToMessageData(v___x_6725_);
    return v___x_6726_;
}
pub unsafe fn _init_l_Lean_Meta_coerceToFunction_x3f___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6728_ = l_Lean_Meta_coerceToFunction_x3f___closed__7;
    v___x_6729_ = l_Lean_stringToMessageData(v___x_6728_);
    return v___x_6729_;
}
pub unsafe fn l_Lean_Meta_coerceToFunction_x3f(
    mut v_expr_6730_: *mut crate::leanh::LeanObject,
    mut v_a_6731_: *mut crate::leanh::LeanObject,
    mut v_a_6732_: *mut crate::leanh::LeanObject,
    mut v_a_6733_: *mut crate::leanh::LeanObject,
    mut v_a_6734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: u8 = 0;
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v_a_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6765_: u8 = 0;
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6773_: u8 = 0;
    let mut v_fst_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6777_: u8 = 0;
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: u8 = 0;
    let mut v___x_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6807_: u8 = 0;
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6811_: u8 = 0;
    let mut v_reuseFailAlloc_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6816_: u8 = 0;
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6820_: u8 = 0;
    let mut v_a_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6824_: u8 = 0;
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6828_: u8 = 0;
    let mut v_isSharedCheck_6829_: u8 = 0;
    let mut v_unused_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6831_: u8 = 0;
    let mut v_a_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6835_: u8 = 0;
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6839_: u8 = 0;
    let mut v_isSharedCheck_6840_: u8 = 0;
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6844_: u8 = 0;
    let mut v_a_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6848_: u8 = 0;
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6852_: u8 = 0;
    let mut v_a_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6856_: u8 = 0;
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6860_: u8 = 0;
    let mut v_a_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6864_: u8 = 0;
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6868_: u8 = 0;
    let mut v_a_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6872_: u8 = 0;
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6876_: u8 = 0;
    let mut v_a_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6880_: u8 = 0;
    let mut v___x_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6884_: u8 = 0;
    let mut v_a_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6888_: u8 = 0;
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6734_);
                crate::leanh::lean_inc_ref(v_a_6733_);
                crate::leanh::lean_inc(v_a_6732_);
                crate::leanh::lean_inc_ref(v_a_6731_);
                crate::leanh::lean_inc_ref(v_expr_6730_);
                v___x_6736_ =
                    lean_infer_type(v_expr_6730_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_);
                if crate::leanh::lean_obj_tag(v___x_6736_) == 0 {
                    v_a_6737_ = crate::leanh::lean_ctor_get(v___x_6736_, 0);
                    crate::leanh::lean_inc_n(v_a_6737_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6736_, 1);
                    v___x_6738_ =
                        l_Lean_Meta_getLevel(v_a_6737_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_);
                    if crate::leanh::lean_obj_tag(v___x_6738_) == 0 {
                        v_a_6739_ = crate::leanh::lean_ctor_get(v___x_6738_, 0);
                        crate::leanh::lean_inc(v_a_6739_);
                        crate::leanh::lean_dec_ref_known(v___x_6738_, 1);
                        v___x_6740_ = l_Lean_Meta_mkFreshLevelMVar(
                            v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6740_) == 0 {
                            v_a_6741_ = crate::leanh::lean_ctor_get(v___x_6740_, 0);
                            crate::leanh::lean_inc_n(v_a_6741_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_6740_, 1);
                            v___x_6742_ = l_Lean_mkSort(v_a_6741_);
                            crate::leanh::lean_inc(v_a_6737_);
                            v___x_6743_ =
                                l_Lean_mkArrow(v_a_6737_, v___x_6742_, v_a_6733_, v_a_6734_);
                            if crate::leanh::lean_obj_tag(v___x_6743_) == 0 {
                                v_a_6744_ = crate::leanh::lean_ctor_get(v___x_6743_, 0);
                                crate::leanh::lean_inc(v_a_6744_);
                                crate::leanh::lean_dec_ref_known(v___x_6743_, 1);
                                v___x_6745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6745_, 0, v_a_6744_);
                                v___x_6746_ = 0;
                                v___x_6747_ = crate::leanh::lean_box(0);
                                v___x_6748_ = l_Lean_Meta_mkFreshExprMVar(
                                    v___x_6745_,
                                    v___x_6746_,
                                    v___x_6747_,
                                    v_a_6731_,
                                    v_a_6732_,
                                    v_a_6733_,
                                    v_a_6734_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6748_) == 0 {
                                    v_a_6749_ = crate::leanh::lean_ctor_get(v___x_6748_, 0);
                                    crate::leanh::lean_inc_n(v_a_6749_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_6748_, 1);
                                    v___x_6750_ = l_Lean_Meta_coerceToFunction_x3f___closed__1;
                                    v___x_6751_ = crate::leanh::lean_box(0);
                                    v___x_6752_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6752_, 0, v_a_6741_);
                                    crate::leanh::lean_ctor_set(v___x_6752_, 1, v___x_6751_);
                                    v___x_6753_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6753_, 0, v_a_6739_);
                                    crate::leanh::lean_ctor_set(v___x_6753_, 1, v___x_6752_);
                                    crate::leanh::lean_inc_ref(v___x_6753_);
                                    v___x_6754_ =
                                        l_Lean_Expr_const___override(v___x_6750_, v___x_6753_);
                                    crate::leanh::lean_inc(v_a_6737_);
                                    v___x_6755_ = l_Lean_mkAppB(v___x_6754_, v_a_6737_, v_a_6749_);
                                    v___x_6756_ = crate::leanh::lean_box(0);
                                    v___x_6757_ = l_Lean_Meta_trySynthInstance(
                                        v___x_6755_,
                                        v___x_6756_,
                                        v_a_6731_,
                                        v_a_6732_,
                                        v_a_6733_,
                                        v_a_6734_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_6757_) == 0 {
                                        v_a_6758_ = crate::leanh::lean_ctor_get(v___x_6757_, 0);
                                        v_isSharedCheck_6844_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6757_)) as u8;
                                        if v_isSharedCheck_6844_ == 0 {
                                            v___x_6760_ = v___x_6757_;
                                            v_isShared_6761_ = v_isSharedCheck_6844_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6758_);
                                            crate::leanh::lean_dec(v___x_6757_);
                                            v___x_6760_ = crate::leanh::lean_box(0);
                                            v_isShared_6761_ = v_isSharedCheck_6844_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_6753_, 2);
                                        crate::leanh::lean_dec(v_a_6749_);
                                        crate::leanh::lean_dec(v_a_6737_);
                                        crate::leanh::lean_dec_ref(v_expr_6730_);
                                        v_a_6845_ = crate::leanh::lean_ctor_get(v___x_6757_, 0);
                                        v_isSharedCheck_6852_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6757_)) as u8;
                                        if v_isSharedCheck_6852_ == 0 {
                                            v___x_6847_ = v___x_6757_;
                                            v_isShared_6848_ = v_isSharedCheck_6852_;
                                            state = 18;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6845_);
                                            crate::leanh::lean_dec(v___x_6757_);
                                            v___x_6847_ = crate::leanh::lean_box(0);
                                            v_isShared_6848_ = v_isSharedCheck_6852_;
                                            state = 18;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6741_);
                                    crate::leanh::lean_dec(v_a_6739_);
                                    crate::leanh::lean_dec(v_a_6737_);
                                    crate::leanh::lean_dec_ref(v_expr_6730_);
                                    v_a_6853_ = crate::leanh::lean_ctor_get(v___x_6748_, 0);
                                    v_isSharedCheck_6860_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6748_)) as u8;
                                    if v_isSharedCheck_6860_ == 0 {
                                        v___x_6855_ = v___x_6748_;
                                        v_isShared_6856_ = v_isSharedCheck_6860_;
                                        state = 20;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6853_);
                                        crate::leanh::lean_dec(v___x_6748_);
                                        v___x_6855_ = crate::leanh::lean_box(0);
                                        v_isShared_6856_ = v_isSharedCheck_6860_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6741_);
                                crate::leanh::lean_dec(v_a_6739_);
                                crate::leanh::lean_dec(v_a_6737_);
                                crate::leanh::lean_dec_ref(v_expr_6730_);
                                v_a_6861_ = crate::leanh::lean_ctor_get(v___x_6743_, 0);
                                v_isSharedCheck_6868_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6743_)) as u8;
                                if v_isSharedCheck_6868_ == 0 {
                                    v___x_6863_ = v___x_6743_;
                                    v_isShared_6864_ = v_isSharedCheck_6868_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6861_);
                                    crate::leanh::lean_dec(v___x_6743_);
                                    v___x_6863_ = crate::leanh::lean_box(0);
                                    v_isShared_6864_ = v_isSharedCheck_6868_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6739_);
                            crate::leanh::lean_dec(v_a_6737_);
                            crate::leanh::lean_dec_ref(v_expr_6730_);
                            v_a_6869_ = crate::leanh::lean_ctor_get(v___x_6740_, 0);
                            v_isSharedCheck_6876_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6740_)) as u8;
                            if v_isSharedCheck_6876_ == 0 {
                                v___x_6871_ = v___x_6740_;
                                v_isShared_6872_ = v_isSharedCheck_6876_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6869_);
                                crate::leanh::lean_dec(v___x_6740_);
                                v___x_6871_ = crate::leanh::lean_box(0);
                                v_isShared_6872_ = v_isSharedCheck_6876_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6737_);
                        crate::leanh::lean_dec_ref(v_expr_6730_);
                        v_a_6877_ = crate::leanh::lean_ctor_get(v___x_6738_, 0);
                        v_isSharedCheck_6884_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6738_)) as u8;
                        if v_isSharedCheck_6884_ == 0 {
                            v___x_6879_ = v___x_6738_;
                            v_isShared_6880_ = v_isSharedCheck_6884_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6877_);
                            crate::leanh::lean_dec(v___x_6738_);
                            v___x_6879_ = crate::leanh::lean_box(0);
                            v_isShared_6880_ = v_isSharedCheck_6884_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_expr_6730_);
                    v_a_6885_ = crate::leanh::lean_ctor_get(v___x_6736_, 0);
                    v_isSharedCheck_6892_ = (!crate::leanh::lean_is_exclusive(v___x_6736_)) as u8;
                    if v_isSharedCheck_6892_ == 0 {
                        v___x_6887_ = v___x_6736_;
                        v_isShared_6888_ = v_isSharedCheck_6892_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6885_);
                        crate::leanh::lean_dec(v___x_6736_);
                        v___x_6887_ = crate::leanh::lean_box(0);
                        v_isShared_6888_ = v_isSharedCheck_6892_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6758_) == 1 {
                    crate::leanh::lean_del_object(v___x_6760_);
                    v_a_6762_ = crate::leanh::lean_ctor_get(v_a_6758_, 0);
                    v_isSharedCheck_6840_ = (!crate::leanh::lean_is_exclusive(v_a_6758_)) as u8;
                    if v_isSharedCheck_6840_ == 0 {
                        v___x_6764_ = v_a_6758_;
                        v_isShared_6765_ = v_isSharedCheck_6840_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6762_);
                        crate::leanh::lean_dec(v_a_6758_);
                        v___x_6764_ = crate::leanh::lean_box(0);
                        v_isShared_6765_ = v_isSharedCheck_6840_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6758_);
                    crate::leanh::lean_dec_ref_known(v___x_6753_, 2);
                    crate::leanh::lean_dec(v_a_6749_);
                    crate::leanh::lean_dec(v_a_6737_);
                    crate::leanh::lean_dec_ref(v_expr_6730_);
                    if v_isShared_6761_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6760_, 0, v___x_6756_);
                        v___x_6842_ = v___x_6760_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_6843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 0, v___x_6756_);
                        v___x_6842_ = v_reuseFailAlloc_6843_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6766_ = l_Lean_Meta_coerceToFunction_x3f___closed__2;
                v___x_6767_ = l_Lean_Expr_const___override(v___x_6766_, v___x_6753_);
                crate::leanh::lean_inc_ref(v_expr_6730_);
                crate::leanh::lean_inc(v_a_6762_);
                v___x_6768_ =
                    l_Lean_mkApp4(v___x_6767_, v_a_6737_, v_a_6749_, v_a_6762_, v_expr_6730_);
                v___x_6769_ =
                    l_Lean_Meta_expandCoe(v___x_6768_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_);
                if crate::leanh::lean_obj_tag(v___x_6769_) == 0 {
                    v_a_6770_ = crate::leanh::lean_ctor_get(v___x_6769_, 0);
                    v_isSharedCheck_6831_ = (!crate::leanh::lean_is_exclusive(v___x_6769_)) as u8;
                    if v_isSharedCheck_6831_ == 0 {
                        v___x_6772_ = v___x_6769_;
                        v_isShared_6773_ = v_isSharedCheck_6831_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6770_);
                        crate::leanh::lean_dec(v___x_6769_);
                        v___x_6772_ = crate::leanh::lean_box(0);
                        v_isShared_6773_ = v_isSharedCheck_6831_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6764_);
                    crate::leanh::lean_dec(v_a_6762_);
                    crate::leanh::lean_dec_ref(v_expr_6730_);
                    v_a_6832_ = crate::leanh::lean_ctor_get(v___x_6769_, 0);
                    v_isSharedCheck_6839_ = (!crate::leanh::lean_is_exclusive(v___x_6769_)) as u8;
                    if v_isSharedCheck_6839_ == 0 {
                        v___x_6834_ = v___x_6769_;
                        v_isShared_6835_ = v_isSharedCheck_6839_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6832_);
                        crate::leanh::lean_dec(v___x_6769_);
                        v___x_6834_ = crate::leanh::lean_box(0);
                        v_isShared_6835_ = v_isSharedCheck_6839_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6774_ = crate::leanh::lean_ctor_get(v_a_6770_, 0);
                v_isSharedCheck_6829_ = (!crate::leanh::lean_is_exclusive(v_a_6770_)) as u8;
                if v_isSharedCheck_6829_ == 0 {
                    v_unused_6830_ = crate::leanh::lean_ctor_get(v_a_6770_, 1);
                    crate::leanh::lean_dec(v_unused_6830_);
                    v___x_6776_ = v_a_6770_;
                    v_isShared_6777_ = v_isSharedCheck_6829_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6774_);
                    crate::leanh::lean_dec(v_a_6770_);
                    v___x_6776_ = crate::leanh::lean_box(0);
                    v_isShared_6777_ = v_isSharedCheck_6829_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_6734_);
                crate::leanh::lean_inc_ref(v_a_6733_);
                crate::leanh::lean_inc(v_a_6732_);
                crate::leanh::lean_inc_ref(v_a_6731_);
                crate::leanh::lean_inc(v_fst_6774_);
                v___x_6785_ =
                    lean_infer_type(v_fst_6774_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_);
                if crate::leanh::lean_obj_tag(v___x_6785_) == 0 {
                    v_a_6786_ = crate::leanh::lean_ctor_get(v___x_6785_, 0);
                    crate::leanh::lean_inc(v_a_6786_);
                    crate::leanh::lean_dec_ref_known(v___x_6785_, 1);
                    crate::leanh::lean_inc(v_a_6734_);
                    crate::leanh::lean_inc_ref(v_a_6733_);
                    crate::leanh::lean_inc(v_a_6732_);
                    crate::leanh::lean_inc_ref(v_a_6731_);
                    v___x_6787_ = lean_whnf(v_a_6786_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_);
                    if crate::leanh::lean_obj_tag(v___x_6787_) == 0 {
                        v_a_6788_ = crate::leanh::lean_ctor_get(v___x_6787_, 0);
                        crate::leanh::lean_inc(v_a_6788_);
                        crate::leanh::lean_dec_ref_known(v___x_6787_, 1);
                        v___x_6789_ = l_Lean_Expr_isForall(v_a_6788_);
                        crate::leanh::lean_dec(v_a_6788_);
                        if v___x_6789_ == 0 {
                            crate::leanh::lean_del_object(v___x_6772_);
                            crate::leanh::lean_del_object(v___x_6764_);
                            v___x_6790_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_coerceToFunction_x3f___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_coerceToFunction_x3f___closed__4_once
                                ),
                                _init_l_Lean_Meta_coerceToFunction_x3f___closed__4,
                            );
                            v___x_6791_ = l_Lean_indentExpr(v_expr_6730_);
                            if v_isShared_6777_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6776_, 7);
                                crate::leanh::lean_ctor_set(v___x_6776_, 1, v___x_6791_);
                                crate::leanh::lean_ctor_set(v___x_6776_, 0, v___x_6790_);
                                v___x_6793_ = v___x_6776_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_6812_ =
                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6812_, 0, v___x_6790_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6812_, 1, v___x_6791_);
                                v___x_6793_ = v_reuseFailAlloc_6812_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6776_);
                            crate::leanh::lean_dec(v_a_6762_);
                            crate::leanh::lean_dec_ref(v_expr_6730_);
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6776_);
                        crate::leanh::lean_dec(v_fst_6774_);
                        crate::leanh::lean_del_object(v___x_6772_);
                        crate::leanh::lean_del_object(v___x_6764_);
                        crate::leanh::lean_dec(v_a_6762_);
                        crate::leanh::lean_dec_ref(v_expr_6730_);
                        v_a_6813_ = crate::leanh::lean_ctor_get(v___x_6787_, 0);
                        v_isSharedCheck_6820_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6787_)) as u8;
                        if v_isSharedCheck_6820_ == 0 {
                            v___x_6815_ = v___x_6787_;
                            v_isShared_6816_ = v_isSharedCheck_6820_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6813_);
                            crate::leanh::lean_dec(v___x_6787_);
                            v___x_6815_ = crate::leanh::lean_box(0);
                            v_isShared_6816_ = v_isSharedCheck_6820_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6776_);
                    crate::leanh::lean_dec(v_fst_6774_);
                    crate::leanh::lean_del_object(v___x_6772_);
                    crate::leanh::lean_del_object(v___x_6764_);
                    crate::leanh::lean_dec(v_a_6762_);
                    crate::leanh::lean_dec_ref(v_expr_6730_);
                    v_a_6821_ = crate::leanh::lean_ctor_get(v___x_6785_, 0);
                    v_isSharedCheck_6828_ = (!crate::leanh::lean_is_exclusive(v___x_6785_)) as u8;
                    if v_isSharedCheck_6828_ == 0 {
                        v___x_6823_ = v___x_6785_;
                        v_isShared_6824_ = v_isSharedCheck_6828_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6821_);
                        crate::leanh::lean_dec(v___x_6785_);
                        v___x_6823_ = crate::leanh::lean_box(0);
                        v_isShared_6824_ = v_isSharedCheck_6828_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6764_, 0, v_fst_6774_);
                    v___x_6780_ = v___x_6764_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_fst_6774_);
                    v___x_6780_ = v_reuseFailAlloc_6784_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6772_, 0, v___x_6780_);
                    v___x_6782_ = v___x_6772_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6783_, 0, v___x_6780_);
                    v___x_6782_ = v_reuseFailAlloc_6783_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6782_;
            }
            8 => {
                v___x_6794_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToFunction_x3f___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToFunction_x3f___closed__6_once),
                    _init_l_Lean_Meta_coerceToFunction_x3f___closed__6,
                );
                v___x_6795_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6795_, 0, v___x_6793_);
                crate::leanh::lean_ctor_set(v___x_6795_, 1, v___x_6794_);
                v___x_6796_ = l_Lean_indentExpr(v_fst_6774_);
                v___x_6797_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6797_, 0, v___x_6795_);
                crate::leanh::lean_ctor_set(v___x_6797_, 1, v___x_6796_);
                v___x_6798_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToFunction_x3f___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToFunction_x3f___closed__8_once),
                    _init_l_Lean_Meta_coerceToFunction_x3f___closed__8,
                );
                v___x_6799_ = l_Lean_indentExpr(v_a_6762_);
                v___x_6800_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6800_, 0, v___x_6798_);
                crate::leanh::lean_ctor_set(v___x_6800_, 1, v___x_6799_);
                v___x_6801_ = l_Lean_MessageData_hint_x27(v___x_6800_);
                v___x_6802_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6802_, 0, v___x_6797_);
                crate::leanh::lean_ctor_set(v___x_6802_, 1, v___x_6801_);
                v___x_6803_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_6802_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_);
                v_a_6804_ = crate::leanh::lean_ctor_get(v___x_6803_, 0);
                v_isSharedCheck_6811_ = (!crate::leanh::lean_is_exclusive(v___x_6803_)) as u8;
                if v_isSharedCheck_6811_ == 0 {
                    v___x_6806_ = v___x_6803_;
                    v_isShared_6807_ = v_isSharedCheck_6811_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6804_);
                    crate::leanh::lean_dec(v___x_6803_);
                    v___x_6806_ = crate::leanh::lean_box(0);
                    v_isShared_6807_ = v_isSharedCheck_6811_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6807_ == 0 {
                    v___x_6809_ = v___x_6806_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_a_6804_);
                    v___x_6809_ = v_reuseFailAlloc_6810_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6809_;
            }
            11 => {
                if v_isShared_6816_ == 0 {
                    v___x_6818_ = v___x_6815_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_a_6813_);
                    v___x_6818_ = v_reuseFailAlloc_6819_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6818_;
            }
            13 => {
                if v_isShared_6824_ == 0 {
                    v___x_6826_ = v___x_6823_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6827_, 0, v_a_6821_);
                    v___x_6826_ = v_reuseFailAlloc_6827_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6826_;
            }
            15 => {
                if v_isShared_6835_ == 0 {
                    v___x_6837_ = v___x_6834_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6838_, 0, v_a_6832_);
                    v___x_6837_ = v_reuseFailAlloc_6838_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6837_;
            }
            17 => {
                return v___x_6842_;
            }
            18 => {
                if v_isShared_6848_ == 0 {
                    v___x_6850_ = v___x_6847_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6851_, 0, v_a_6845_);
                    v___x_6850_ = v_reuseFailAlloc_6851_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6850_;
            }
            20 => {
                if v_isShared_6856_ == 0 {
                    v___x_6858_ = v___x_6855_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6859_, 0, v_a_6853_);
                    v___x_6858_ = v_reuseFailAlloc_6859_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6858_;
            }
            22 => {
                if v_isShared_6864_ == 0 {
                    v___x_6866_ = v___x_6863_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6867_, 0, v_a_6861_);
                    v___x_6866_ = v_reuseFailAlloc_6867_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6866_;
            }
            24 => {
                if v_isShared_6872_ == 0 {
                    v___x_6874_ = v___x_6871_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6875_, 0, v_a_6869_);
                    v___x_6874_ = v_reuseFailAlloc_6875_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6874_;
            }
            26 => {
                if v_isShared_6880_ == 0 {
                    v___x_6882_ = v___x_6879_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_a_6877_);
                    v___x_6882_ = v_reuseFailAlloc_6883_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6882_;
            }
            28 => {
                if v_isShared_6888_ == 0 {
                    v___x_6890_ = v___x_6887_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6891_, 0, v_a_6885_);
                    v___x_6890_ = v_reuseFailAlloc_6891_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerceToFunction_x3f___boxed(
    mut v_expr_6893_: *mut crate::leanh::LeanObject,
    mut v_a_6894_: *mut crate::leanh::LeanObject,
    mut v_a_6895_: *mut crate::leanh::LeanObject,
    mut v_a_6896_: *mut crate::leanh::LeanObject,
    mut v_a_6897_: *mut crate::leanh::LeanObject,
    mut v_a_6898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6899_ =
        l_Lean_Meta_coerceToFunction_x3f(v_expr_6893_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_);
    crate::leanh::lean_dec(v_a_6897_);
    crate::leanh::lean_dec_ref(v_a_6896_);
    crate::leanh::lean_dec(v_a_6895_);
    crate::leanh::lean_dec_ref(v_a_6894_);
    return v_res_6899_;
}
pub unsafe fn _init_l_Lean_Meta_coerceToSort_x3f___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6907_ = l_Lean_Meta_coerceToSort_x3f___closed__3;
    v___x_6908_ = l_Lean_stringToMessageData(v___x_6907_);
    return v___x_6908_;
}
pub unsafe fn _init_l_Lean_Meta_coerceToSort_x3f___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6910_ = l_Lean_Meta_coerceToSort_x3f___closed__5;
    v___x_6911_ = l_Lean_stringToMessageData(v___x_6910_);
    return v___x_6911_;
}
pub unsafe fn l_Lean_Meta_coerceToSort_x3f(
    mut v_expr_6912_: *mut crate::leanh::LeanObject,
    mut v_a_6913_: *mut crate::leanh::LeanObject,
    mut v_a_6914_: *mut crate::leanh::LeanObject,
    mut v_a_6915_: *mut crate::leanh::LeanObject,
    mut v_a_6916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: u8 = 0;
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6941_: u8 = 0;
    let mut v_a_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6945_: u8 = 0;
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6953_: u8 = 0;
    let mut v_fst_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6957_: u8 = 0;
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: u8 = 0;
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6987_: u8 = 0;
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6991_: u8 = 0;
    let mut v_reuseFailAlloc_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6996_: u8 = 0;
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7000_: u8 = 0;
    let mut v_a_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7004_: u8 = 0;
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7008_: u8 = 0;
    let mut v_isSharedCheck_7009_: u8 = 0;
    let mut v_unused_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7011_: u8 = 0;
    let mut v_a_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7015_: u8 = 0;
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7019_: u8 = 0;
    let mut v_isSharedCheck_7020_: u8 = 0;
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7024_: u8 = 0;
    let mut v_a_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7028_: u8 = 0;
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7032_: u8 = 0;
    let mut v_a_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7036_: u8 = 0;
    let mut v___x_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7040_: u8 = 0;
    let mut v_a_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7044_: u8 = 0;
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7048_: u8 = 0;
    let mut v_a_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7052_: u8 = 0;
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7056_: u8 = 0;
    let mut v_a_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7060_: u8 = 0;
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6916_);
                crate::leanh::lean_inc_ref(v_a_6915_);
                crate::leanh::lean_inc(v_a_6914_);
                crate::leanh::lean_inc_ref(v_a_6913_);
                crate::leanh::lean_inc_ref(v_expr_6912_);
                v___x_6918_ =
                    lean_infer_type(v_expr_6912_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
                if crate::leanh::lean_obj_tag(v___x_6918_) == 0 {
                    v_a_6919_ = crate::leanh::lean_ctor_get(v___x_6918_, 0);
                    crate::leanh::lean_inc_n(v_a_6919_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6918_, 1);
                    v___x_6920_ =
                        l_Lean_Meta_getLevel(v_a_6919_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
                    if crate::leanh::lean_obj_tag(v___x_6920_) == 0 {
                        v_a_6921_ = crate::leanh::lean_ctor_get(v___x_6920_, 0);
                        crate::leanh::lean_inc(v_a_6921_);
                        crate::leanh::lean_dec_ref_known(v___x_6920_, 1);
                        v___x_6922_ = l_Lean_Meta_mkFreshLevelMVar(
                            v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6922_) == 0 {
                            v_a_6923_ = crate::leanh::lean_ctor_get(v___x_6922_, 0);
                            crate::leanh::lean_inc_n(v_a_6923_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_6922_, 1);
                            v___x_6924_ = l_Lean_mkSort(v_a_6923_);
                            v___x_6925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6925_, 0, v___x_6924_);
                            v___x_6926_ = 0;
                            v___x_6927_ = crate::leanh::lean_box(0);
                            v___x_6928_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_6925_,
                                v___x_6926_,
                                v___x_6927_,
                                v_a_6913_,
                                v_a_6914_,
                                v_a_6915_,
                                v_a_6916_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6928_) == 0 {
                                v_a_6929_ = crate::leanh::lean_ctor_get(v___x_6928_, 0);
                                crate::leanh::lean_inc_n(v_a_6929_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_6928_, 1);
                                v___x_6930_ = l_Lean_Meta_coerceToSort_x3f___closed__1;
                                v___x_6931_ = crate::leanh::lean_box(0);
                                v___x_6932_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6932_, 0, v_a_6923_);
                                crate::leanh::lean_ctor_set(v___x_6932_, 1, v___x_6931_);
                                v___x_6933_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6933_, 0, v_a_6921_);
                                crate::leanh::lean_ctor_set(v___x_6933_, 1, v___x_6932_);
                                crate::leanh::lean_inc_ref(v___x_6933_);
                                v___x_6934_ =
                                    l_Lean_Expr_const___override(v___x_6930_, v___x_6933_);
                                crate::leanh::lean_inc(v_a_6919_);
                                v___x_6935_ = l_Lean_mkAppB(v___x_6934_, v_a_6919_, v_a_6929_);
                                v___x_6936_ = crate::leanh::lean_box(0);
                                v___x_6937_ = l_Lean_Meta_trySynthInstance(
                                    v___x_6935_,
                                    v___x_6936_,
                                    v_a_6913_,
                                    v_a_6914_,
                                    v_a_6915_,
                                    v_a_6916_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6937_) == 0 {
                                    v_a_6938_ = crate::leanh::lean_ctor_get(v___x_6937_, 0);
                                    v_isSharedCheck_7024_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6937_)) as u8;
                                    if v_isSharedCheck_7024_ == 0 {
                                        v___x_6940_ = v___x_6937_;
                                        v_isShared_6941_ = v_isSharedCheck_7024_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6938_);
                                        crate::leanh::lean_dec(v___x_6937_);
                                        v___x_6940_ = crate::leanh::lean_box(0);
                                        v_isShared_6941_ = v_isSharedCheck_7024_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_6933_, 2);
                                    crate::leanh::lean_dec(v_a_6929_);
                                    crate::leanh::lean_dec(v_a_6919_);
                                    crate::leanh::lean_dec_ref(v_expr_6912_);
                                    v_a_7025_ = crate::leanh::lean_ctor_get(v___x_6937_, 0);
                                    v_isSharedCheck_7032_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6937_)) as u8;
                                    if v_isSharedCheck_7032_ == 0 {
                                        v___x_7027_ = v___x_6937_;
                                        v_isShared_7028_ = v_isSharedCheck_7032_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7025_);
                                        crate::leanh::lean_dec(v___x_6937_);
                                        v___x_7027_ = crate::leanh::lean_box(0);
                                        v_isShared_7028_ = v_isSharedCheck_7032_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6923_);
                                crate::leanh::lean_dec(v_a_6921_);
                                crate::leanh::lean_dec(v_a_6919_);
                                crate::leanh::lean_dec_ref(v_expr_6912_);
                                v_a_7033_ = crate::leanh::lean_ctor_get(v___x_6928_, 0);
                                v_isSharedCheck_7040_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6928_)) as u8;
                                if v_isSharedCheck_7040_ == 0 {
                                    v___x_7035_ = v___x_6928_;
                                    v_isShared_7036_ = v_isSharedCheck_7040_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7033_);
                                    crate::leanh::lean_dec(v___x_6928_);
                                    v___x_7035_ = crate::leanh::lean_box(0);
                                    v_isShared_7036_ = v_isSharedCheck_7040_;
                                    state = 20;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6921_);
                            crate::leanh::lean_dec(v_a_6919_);
                            crate::leanh::lean_dec_ref(v_expr_6912_);
                            v_a_7041_ = crate::leanh::lean_ctor_get(v___x_6922_, 0);
                            v_isSharedCheck_7048_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6922_)) as u8;
                            if v_isSharedCheck_7048_ == 0 {
                                v___x_7043_ = v___x_6922_;
                                v_isShared_7044_ = v_isSharedCheck_7048_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7041_);
                                crate::leanh::lean_dec(v___x_6922_);
                                v___x_7043_ = crate::leanh::lean_box(0);
                                v_isShared_7044_ = v_isSharedCheck_7048_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6919_);
                        crate::leanh::lean_dec_ref(v_expr_6912_);
                        v_a_7049_ = crate::leanh::lean_ctor_get(v___x_6920_, 0);
                        v_isSharedCheck_7056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6920_)) as u8;
                        if v_isSharedCheck_7056_ == 0 {
                            v___x_7051_ = v___x_6920_;
                            v_isShared_7052_ = v_isSharedCheck_7056_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7049_);
                            crate::leanh::lean_dec(v___x_6920_);
                            v___x_7051_ = crate::leanh::lean_box(0);
                            v_isShared_7052_ = v_isSharedCheck_7056_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_expr_6912_);
                    v_a_7057_ = crate::leanh::lean_ctor_get(v___x_6918_, 0);
                    v_isSharedCheck_7064_ = (!crate::leanh::lean_is_exclusive(v___x_6918_)) as u8;
                    if v_isSharedCheck_7064_ == 0 {
                        v___x_7059_ = v___x_6918_;
                        v_isShared_7060_ = v_isSharedCheck_7064_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7057_);
                        crate::leanh::lean_dec(v___x_6918_);
                        v___x_7059_ = crate::leanh::lean_box(0);
                        v_isShared_7060_ = v_isSharedCheck_7064_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6938_) == 1 {
                    crate::leanh::lean_del_object(v___x_6940_);
                    v_a_6942_ = crate::leanh::lean_ctor_get(v_a_6938_, 0);
                    v_isSharedCheck_7020_ = (!crate::leanh::lean_is_exclusive(v_a_6938_)) as u8;
                    if v_isSharedCheck_7020_ == 0 {
                        v___x_6944_ = v_a_6938_;
                        v_isShared_6945_ = v_isSharedCheck_7020_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6942_);
                        crate::leanh::lean_dec(v_a_6938_);
                        v___x_6944_ = crate::leanh::lean_box(0);
                        v_isShared_6945_ = v_isSharedCheck_7020_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6938_);
                    crate::leanh::lean_dec_ref_known(v___x_6933_, 2);
                    crate::leanh::lean_dec(v_a_6929_);
                    crate::leanh::lean_dec(v_a_6919_);
                    crate::leanh::lean_dec_ref(v_expr_6912_);
                    if v_isShared_6941_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6940_, 0, v___x_6936_);
                        v___x_7022_ = v___x_6940_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_7023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7023_, 0, v___x_6936_);
                        v___x_7022_ = v_reuseFailAlloc_7023_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6946_ = l_Lean_Meta_coerceToSort_x3f___closed__2;
                v___x_6947_ = l_Lean_Expr_const___override(v___x_6946_, v___x_6933_);
                crate::leanh::lean_inc_ref(v_expr_6912_);
                crate::leanh::lean_inc(v_a_6942_);
                v___x_6948_ =
                    l_Lean_mkApp4(v___x_6947_, v_a_6919_, v_a_6929_, v_a_6942_, v_expr_6912_);
                v___x_6949_ =
                    l_Lean_Meta_expandCoe(v___x_6948_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
                if crate::leanh::lean_obj_tag(v___x_6949_) == 0 {
                    v_a_6950_ = crate::leanh::lean_ctor_get(v___x_6949_, 0);
                    v_isSharedCheck_7011_ = (!crate::leanh::lean_is_exclusive(v___x_6949_)) as u8;
                    if v_isSharedCheck_7011_ == 0 {
                        v___x_6952_ = v___x_6949_;
                        v_isShared_6953_ = v_isSharedCheck_7011_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6950_);
                        crate::leanh::lean_dec(v___x_6949_);
                        v___x_6952_ = crate::leanh::lean_box(0);
                        v_isShared_6953_ = v_isSharedCheck_7011_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6944_);
                    crate::leanh::lean_dec(v_a_6942_);
                    crate::leanh::lean_dec_ref(v_expr_6912_);
                    v_a_7012_ = crate::leanh::lean_ctor_get(v___x_6949_, 0);
                    v_isSharedCheck_7019_ = (!crate::leanh::lean_is_exclusive(v___x_6949_)) as u8;
                    if v_isSharedCheck_7019_ == 0 {
                        v___x_7014_ = v___x_6949_;
                        v_isShared_7015_ = v_isSharedCheck_7019_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7012_);
                        crate::leanh::lean_dec(v___x_6949_);
                        v___x_7014_ = crate::leanh::lean_box(0);
                        v_isShared_7015_ = v_isSharedCheck_7019_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6954_ = crate::leanh::lean_ctor_get(v_a_6950_, 0);
                v_isSharedCheck_7009_ = (!crate::leanh::lean_is_exclusive(v_a_6950_)) as u8;
                if v_isSharedCheck_7009_ == 0 {
                    v_unused_7010_ = crate::leanh::lean_ctor_get(v_a_6950_, 1);
                    crate::leanh::lean_dec(v_unused_7010_);
                    v___x_6956_ = v_a_6950_;
                    v_isShared_6957_ = v_isSharedCheck_7009_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6954_);
                    crate::leanh::lean_dec(v_a_6950_);
                    v___x_6956_ = crate::leanh::lean_box(0);
                    v_isShared_6957_ = v_isSharedCheck_7009_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_6916_);
                crate::leanh::lean_inc_ref(v_a_6915_);
                crate::leanh::lean_inc(v_a_6914_);
                crate::leanh::lean_inc_ref(v_a_6913_);
                crate::leanh::lean_inc(v_fst_6954_);
                v___x_6965_ =
                    lean_infer_type(v_fst_6954_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
                if crate::leanh::lean_obj_tag(v___x_6965_) == 0 {
                    v_a_6966_ = crate::leanh::lean_ctor_get(v___x_6965_, 0);
                    crate::leanh::lean_inc(v_a_6966_);
                    crate::leanh::lean_dec_ref_known(v___x_6965_, 1);
                    crate::leanh::lean_inc(v_a_6916_);
                    crate::leanh::lean_inc_ref(v_a_6915_);
                    crate::leanh::lean_inc(v_a_6914_);
                    crate::leanh::lean_inc_ref(v_a_6913_);
                    v___x_6967_ = lean_whnf(v_a_6966_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
                    if crate::leanh::lean_obj_tag(v___x_6967_) == 0 {
                        v_a_6968_ = crate::leanh::lean_ctor_get(v___x_6967_, 0);
                        crate::leanh::lean_inc(v_a_6968_);
                        crate::leanh::lean_dec_ref_known(v___x_6967_, 1);
                        v___x_6969_ = l_Lean_Expr_isSort(v_a_6968_);
                        crate::leanh::lean_dec(v_a_6968_);
                        if v___x_6969_ == 0 {
                            crate::leanh::lean_del_object(v___x_6952_);
                            crate::leanh::lean_del_object(v___x_6944_);
                            v___x_6970_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_coerceToFunction_x3f___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_coerceToFunction_x3f___closed__4_once
                                ),
                                _init_l_Lean_Meta_coerceToFunction_x3f___closed__4,
                            );
                            v___x_6971_ = l_Lean_indentExpr(v_expr_6912_);
                            if v_isShared_6957_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6956_, 7);
                                crate::leanh::lean_ctor_set(v___x_6956_, 1, v___x_6971_);
                                crate::leanh::lean_ctor_set(v___x_6956_, 0, v___x_6970_);
                                v___x_6973_ = v___x_6956_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_6992_ =
                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6992_, 0, v___x_6970_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6992_, 1, v___x_6971_);
                                v___x_6973_ = v_reuseFailAlloc_6992_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6956_);
                            crate::leanh::lean_dec(v_a_6942_);
                            crate::leanh::lean_dec_ref(v_expr_6912_);
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6956_);
                        crate::leanh::lean_dec(v_fst_6954_);
                        crate::leanh::lean_del_object(v___x_6952_);
                        crate::leanh::lean_del_object(v___x_6944_);
                        crate::leanh::lean_dec(v_a_6942_);
                        crate::leanh::lean_dec_ref(v_expr_6912_);
                        v_a_6993_ = crate::leanh::lean_ctor_get(v___x_6967_, 0);
                        v_isSharedCheck_7000_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6967_)) as u8;
                        if v_isSharedCheck_7000_ == 0 {
                            v___x_6995_ = v___x_6967_;
                            v_isShared_6996_ = v_isSharedCheck_7000_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6993_);
                            crate::leanh::lean_dec(v___x_6967_);
                            v___x_6995_ = crate::leanh::lean_box(0);
                            v_isShared_6996_ = v_isSharedCheck_7000_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6956_);
                    crate::leanh::lean_dec(v_fst_6954_);
                    crate::leanh::lean_del_object(v___x_6952_);
                    crate::leanh::lean_del_object(v___x_6944_);
                    crate::leanh::lean_dec(v_a_6942_);
                    crate::leanh::lean_dec_ref(v_expr_6912_);
                    v_a_7001_ = crate::leanh::lean_ctor_get(v___x_6965_, 0);
                    v_isSharedCheck_7008_ = (!crate::leanh::lean_is_exclusive(v___x_6965_)) as u8;
                    if v_isSharedCheck_7008_ == 0 {
                        v___x_7003_ = v___x_6965_;
                        v_isShared_7004_ = v_isSharedCheck_7008_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7001_);
                        crate::leanh::lean_dec(v___x_6965_);
                        v___x_7003_ = crate::leanh::lean_box(0);
                        v_isShared_7004_ = v_isSharedCheck_7008_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6944_, 0, v_fst_6954_);
                    v___x_6960_ = v___x_6944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 0, v_fst_6954_);
                    v___x_6960_ = v_reuseFailAlloc_6964_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6952_, 0, v___x_6960_);
                    v___x_6962_ = v___x_6952_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6963_, 0, v___x_6960_);
                    v___x_6962_ = v_reuseFailAlloc_6963_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6962_;
            }
            8 => {
                v___x_6974_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToSort_x3f___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToSort_x3f___closed__4_once),
                    _init_l_Lean_Meta_coerceToSort_x3f___closed__4,
                );
                v___x_6975_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6975_, 0, v___x_6973_);
                crate::leanh::lean_ctor_set(v___x_6975_, 1, v___x_6974_);
                v___x_6976_ = l_Lean_indentExpr(v_fst_6954_);
                v___x_6977_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6977_, 0, v___x_6975_);
                crate::leanh::lean_ctor_set(v___x_6977_, 1, v___x_6976_);
                v___x_6978_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToSort_x3f___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Meta_coerceToSort_x3f___closed__6_once),
                    _init_l_Lean_Meta_coerceToSort_x3f___closed__6,
                );
                v___x_6979_ = l_Lean_indentExpr(v_a_6942_);
                v___x_6980_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6980_, 0, v___x_6978_);
                crate::leanh::lean_ctor_set(v___x_6980_, 1, v___x_6979_);
                v___x_6981_ = l_Lean_MessageData_hint_x27(v___x_6980_);
                v___x_6982_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6982_, 0, v___x_6977_);
                crate::leanh::lean_ctor_set(v___x_6982_, 1, v___x_6981_);
                v___x_6983_ = l_Lean_throwError___at___00Lean_Meta_coerceSimpleRecordingNames_x3f_spec__0___redArg(v___x_6982_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
                v_a_6984_ = crate::leanh::lean_ctor_get(v___x_6983_, 0);
                v_isSharedCheck_6991_ = (!crate::leanh::lean_is_exclusive(v___x_6983_)) as u8;
                if v_isSharedCheck_6991_ == 0 {
                    v___x_6986_ = v___x_6983_;
                    v_isShared_6987_ = v_isSharedCheck_6991_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6984_);
                    crate::leanh::lean_dec(v___x_6983_);
                    v___x_6986_ = crate::leanh::lean_box(0);
                    v_isShared_6987_ = v_isSharedCheck_6991_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6987_ == 0 {
                    v___x_6989_ = v___x_6986_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6990_, 0, v_a_6984_);
                    v___x_6989_ = v_reuseFailAlloc_6990_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6989_;
            }
            11 => {
                if v_isShared_6996_ == 0 {
                    v___x_6998_ = v___x_6995_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6999_, 0, v_a_6993_);
                    v___x_6998_ = v_reuseFailAlloc_6999_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6998_;
            }
            13 => {
                if v_isShared_7004_ == 0 {
                    v___x_7006_ = v___x_7003_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 0, v_a_7001_);
                    v___x_7006_ = v_reuseFailAlloc_7007_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7006_;
            }
            15 => {
                if v_isShared_7015_ == 0 {
                    v___x_7017_ = v___x_7014_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7018_, 0, v_a_7012_);
                    v___x_7017_ = v_reuseFailAlloc_7018_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7017_;
            }
            17 => {
                return v___x_7022_;
            }
            18 => {
                if v_isShared_7028_ == 0 {
                    v___x_7030_ = v___x_7027_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7031_, 0, v_a_7025_);
                    v___x_7030_ = v_reuseFailAlloc_7031_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7030_;
            }
            20 => {
                if v_isShared_7036_ == 0 {
                    v___x_7038_ = v___x_7035_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7039_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7039_, 0, v_a_7033_);
                    v___x_7038_ = v_reuseFailAlloc_7039_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7038_;
            }
            22 => {
                if v_isShared_7044_ == 0 {
                    v___x_7046_ = v___x_7043_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7047_, 0, v_a_7041_);
                    v___x_7046_ = v_reuseFailAlloc_7047_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7046_;
            }
            24 => {
                if v_isShared_7052_ == 0 {
                    v___x_7054_ = v___x_7051_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7055_, 0, v_a_7049_);
                    v___x_7054_ = v_reuseFailAlloc_7055_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7054_;
            }
            26 => {
                if v_isShared_7060_ == 0 {
                    v___x_7062_ = v___x_7059_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7063_, 0, v_a_7057_);
                    v___x_7062_ = v_reuseFailAlloc_7063_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_7062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerceToSort_x3f___boxed(
    mut v_expr_7065_: *mut crate::leanh::LeanObject,
    mut v_a_7066_: *mut crate::leanh::LeanObject,
    mut v_a_7067_: *mut crate::leanh::LeanObject,
    mut v_a_7068_: *mut crate::leanh::LeanObject,
    mut v_a_7069_: *mut crate::leanh::LeanObject,
    mut v_a_7070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7071_ =
        l_Lean_Meta_coerceToSort_x3f(v_expr_7065_, v_a_7066_, v_a_7067_, v_a_7068_, v_a_7069_);
    crate::leanh::lean_dec(v_a_7069_);
    crate::leanh::lean_dec_ref(v_a_7068_);
    crate::leanh::lean_dec(v_a_7067_);
    crate::leanh::lean_dec_ref(v_a_7066_);
    return v_res_7071_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
    mut v_e_7072_: *mut crate::leanh::LeanObject,
    mut v___y_7073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7075_: u8 = 0;
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7089_: u8 = 0;
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7095_: u8 = 0;
    let mut v_unused_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7075_ = l_Lean_Expr_hasMVar(v_e_7072_);
                if v___x_7075_ == 0 {
                    v___x_7076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7076_, 0, v_e_7072_);
                    return v___x_7076_;
                } else {
                    v___x_7077_ = lean_st_ref_get(v___y_7073_);
                    v_mctx_7078_ = crate::leanh::lean_ctor_get(v___x_7077_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_7078_);
                    crate::leanh::lean_dec(v___x_7077_);
                    v___x_7079_ = l_Lean_instantiateMVarsCore(v_mctx_7078_, v_e_7072_);
                    v_fst_7080_ = crate::leanh::lean_ctor_get(v___x_7079_, 0);
                    crate::leanh::lean_inc(v_fst_7080_);
                    v_snd_7081_ = crate::leanh::lean_ctor_get(v___x_7079_, 1);
                    crate::leanh::lean_inc(v_snd_7081_);
                    crate::leanh::lean_dec_ref(v___x_7079_);
                    v___x_7082_ = lean_st_ref_take(v___y_7073_);
                    v_cache_7083_ = crate::leanh::lean_ctor_get(v___x_7082_, 1);
                    v_zetaDeltaFVarIds_7084_ = crate::leanh::lean_ctor_get(v___x_7082_, 2);
                    v_postponed_7085_ = crate::leanh::lean_ctor_get(v___x_7082_, 3);
                    v_diag_7086_ = crate::leanh::lean_ctor_get(v___x_7082_, 4);
                    v_isSharedCheck_7095_ = (!crate::leanh::lean_is_exclusive(v___x_7082_)) as u8;
                    if v_isSharedCheck_7095_ == 0 {
                        v_unused_7096_ = crate::leanh::lean_ctor_get(v___x_7082_, 0);
                        crate::leanh::lean_dec(v_unused_7096_);
                        v___x_7088_ = v___x_7082_;
                        v_isShared_7089_ = v_isSharedCheck_7095_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_7086_);
                        crate::leanh::lean_inc(v_postponed_7085_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_7084_);
                        crate::leanh::lean_inc(v_cache_7083_);
                        crate::leanh::lean_dec(v___x_7082_);
                        v___x_7088_ = crate::leanh::lean_box(0);
                        v_isShared_7089_ = v_isSharedCheck_7095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7088_, 0, v_snd_7081_);
                    v___x_7091_ = v___x_7088_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7094_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7094_, 0, v_snd_7081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7094_, 1, v_cache_7083_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7094_,
                        2,
                        v_zetaDeltaFVarIds_7084_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7094_, 3, v_postponed_7085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7094_, 4, v_diag_7086_);
                    v___x_7091_ = v_reuseFailAlloc_7094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7092_ = lean_st_ref_set(v___y_7073_, v___x_7091_);
                v___x_7093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7093_, 0, v_fst_7080_);
                return v___x_7093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg___boxed(
    mut v_e_7097_: *mut crate::leanh::LeanObject,
    mut v___y_7098_: *mut crate::leanh::LeanObject,
    mut v___y_7099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7100_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
        v_e_7097_,
        v___y_7098_,
    );
    crate::leanh::lean_dec(v___y_7098_);
    return v_res_7100_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(
    mut v_e_7101_: *mut crate::leanh::LeanObject,
    mut v___y_7102_: *mut crate::leanh::LeanObject,
    mut v___y_7103_: *mut crate::leanh::LeanObject,
    mut v___y_7104_: *mut crate::leanh::LeanObject,
    mut v___y_7105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7107_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
        v_e_7101_,
        v___y_7103_,
    );
    return v___x_7107_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___boxed(
    mut v_e_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
    mut v___y_7110_: *mut crate::leanh::LeanObject,
    mut v___y_7111_: *mut crate::leanh::LeanObject,
    mut v___y_7112_: *mut crate::leanh::LeanObject,
    mut v___y_7113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7114_ = l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0(
        v_e_7108_,
        v___y_7109_,
        v___y_7110_,
        v___y_7111_,
        v___y_7112_,
    );
    crate::leanh::lean_dec(v___y_7112_);
    crate::leanh::lean_dec_ref(v___y_7111_);
    crate::leanh::lean_dec(v___y_7110_);
    crate::leanh::lean_dec_ref(v___y_7109_);
    return v_res_7114_;
}
pub unsafe fn _init_l_Lean_Meta_isTypeApp_x3f___closed__0() -> u64 {
    let mut v___x_7115_: u8 = 0;
    let mut v___x_7116_: u64 = 0;
    v___x_7115_ = 2;
    v___x_7116_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_7115_);
    return v___x_7116_;
}
pub unsafe fn l_Lean_Meta_isTypeApp_x3f(
    mut v_type_7117_: *mut crate::leanh::LeanObject,
    mut v_a_7118_: *mut crate::leanh::LeanObject,
    mut v_a_7119_: *mut crate::leanh::LeanObject,
    mut v_a_7120_: *mut crate::leanh::LeanObject,
    mut v_a_7121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_7124_: u8 = 0;
    let mut v_ctxApprox_7125_: u8 = 0;
    let mut v_quasiPatternApprox_7126_: u8 = 0;
    let mut v_constApprox_7127_: u8 = 0;
    let mut v_isDefEqStuckEx_7128_: u8 = 0;
    let mut v_unificationHints_7129_: u8 = 0;
    let mut v_proofIrrelevance_7130_: u8 = 0;
    let mut v_assignSyntheticOpaque_7131_: u8 = 0;
    let mut v_offsetCnstrs_7132_: u8 = 0;
    let mut v_etaStruct_7133_: u8 = 0;
    let mut v_univApprox_7134_: u8 = 0;
    let mut v_iota_7135_: u8 = 0;
    let mut v_beta_7136_: u8 = 0;
    let mut v_proj_7137_: u8 = 0;
    let mut v_zeta_7138_: u8 = 0;
    let mut v_zetaDelta_7139_: u8 = 0;
    let mut v_zetaUnused_7140_: u8 = 0;
    let mut v_zetaHave_7141_: u8 = 0;
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7144_: u8 = 0;
    let mut v_trackZetaDelta_7145_: u8 = 0;
    let mut v_zetaDeltaSet_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7152_: u8 = 0;
    let mut v_inTypeClassResolution_7153_: u8 = 0;
    let mut v_cacheInferType_7154_: u8 = 0;
    let mut v___x_7155_: u8 = 0;
    let mut v_config_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: u64 = 0;
    let mut v___x_7159_: u64 = 0;
    let mut v___x_7160_: u64 = 0;
    let mut v___x_7161_: u64 = 0;
    let mut v___x_7162_: u64 = 0;
    let mut v_key_7163_: u64 = 0;
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7170_: u8 = 0;
    let mut v_fn_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7177_: u8 = 0;
    let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7182_: u8 = 0;
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7190_: u8 = 0;
    let mut v_isSharedCheck_7191_: u8 = 0;
    let mut v___x_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7196_: u8 = 0;
    let mut v_a_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7200_: u8 = 0;
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7204_: u8 = 0;
    let mut v_reuseFailAlloc_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7123_ = l_Lean_Meta_Context_config(v_a_7118_);
                v_foApprox_7124_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 0 as u32);
                v_ctxApprox_7125_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 1 as u32);
                v_quasiPatternApprox_7126_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_7123_, 2 as u32);
                v_constApprox_7127_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 3 as u32);
                v_isDefEqStuckEx_7128_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 4 as u32);
                v_unificationHints_7129_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 5 as u32);
                v_proofIrrelevance_7130_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 6 as u32);
                v_assignSyntheticOpaque_7131_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_7123_, 7 as u32);
                v_offsetCnstrs_7132_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 8 as u32);
                v_etaStruct_7133_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 10 as u32);
                v_univApprox_7134_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 11 as u32);
                v_iota_7135_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 12 as u32);
                v_beta_7136_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 13 as u32);
                v_proj_7137_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 14 as u32);
                v_zeta_7138_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 15 as u32);
                v_zetaDelta_7139_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 16 as u32);
                v_zetaUnused_7140_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 17 as u32);
                v_zetaHave_7141_ = crate::leanh::lean_ctor_get_uint8(v___x_7123_, 18 as u32);
                v_isSharedCheck_7206_ = (!crate::leanh::lean_is_exclusive(v___x_7123_)) as u8;
                if v_isSharedCheck_7206_ == 0 {
                    v___x_7143_ = v___x_7123_;
                    v_isShared_7144_ = v_isSharedCheck_7206_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_7123_);
                    v___x_7143_ = crate::leanh::lean_box(0);
                    v_isShared_7144_ = v_isSharedCheck_7206_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_7145_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_7118_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_7146_ = crate::leanh::lean_ctor_get(v_a_7118_, 1);
                v_lctx_7147_ = crate::leanh::lean_ctor_get(v_a_7118_, 2);
                v_localInstances_7148_ = crate::leanh::lean_ctor_get(v_a_7118_, 3);
                v_defEqCtx_x3f_7149_ = crate::leanh::lean_ctor_get(v_a_7118_, 4);
                v_synthPendingDepth_7150_ = crate::leanh::lean_ctor_get(v_a_7118_, 5);
                v_canUnfold_x3f_7151_ = crate::leanh::lean_ctor_get(v_a_7118_, 6);
                v_univApprox_7152_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_7118_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7153_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_7118_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7154_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_7118_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_7155_ = 2;
                if v_isShared_7144_ == 0 {
                    v_config_7157_ = v___x_7143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7205_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        0 as u32,
                        v_foApprox_7124_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        1 as u32,
                        v_ctxApprox_7125_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        2 as u32,
                        v_quasiPatternApprox_7126_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        3 as u32,
                        v_constApprox_7127_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        4 as u32,
                        v_isDefEqStuckEx_7128_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        5 as u32,
                        v_unificationHints_7129_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        6 as u32,
                        v_proofIrrelevance_7130_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        7 as u32,
                        v_assignSyntheticOpaque_7131_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        8 as u32,
                        v_offsetCnstrs_7132_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        10 as u32,
                        v_etaStruct_7133_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        11 as u32,
                        v_univApprox_7134_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        12 as u32,
                        v_iota_7135_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        13 as u32,
                        v_beta_7136_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        14 as u32,
                        v_proj_7137_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        15 as u32,
                        v_zeta_7138_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        16 as u32,
                        v_zetaDelta_7139_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        17 as u32,
                        v_zetaUnused_7140_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7205_,
                        18 as u32,
                        v_zetaHave_7141_,
                    );
                    v_config_7157_ = v_reuseFailAlloc_7205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_7157_, 9 as u32, v___x_7155_);
                v___x_7158_ = l_Lean_Meta_Context_configKey(v_a_7118_);
                v___x_7159_ = 3u64;
                v___x_7160_ = lean_uint64_shift_right(v___x_7158_, v___x_7159_);
                v___x_7161_ = lean_uint64_shift_left(v___x_7160_, v___x_7159_);
                v___x_7162_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_isTypeApp_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_isTypeApp_x3f___closed__0_once),
                    _init_l_Lean_Meta_isTypeApp_x3f___closed__0,
                );
                v_key_7163_ = lean_uint64_lor(v___x_7161_, v___x_7162_);
                v___x_7164_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_7164_, 0, v_config_7157_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_7164_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_7163_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_7151_);
                crate::leanh::lean_inc(v_synthPendingDepth_7150_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_7149_);
                crate::leanh::lean_inc_ref(v_localInstances_7148_);
                crate::leanh::lean_inc_ref(v_lctx_7147_);
                crate::leanh::lean_inc(v_zetaDeltaSet_7146_);
                v___x_7165_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_7165_, 0, v___x_7164_);
                crate::leanh::lean_ctor_set(v___x_7165_, 1, v_zetaDeltaSet_7146_);
                crate::leanh::lean_ctor_set(v___x_7165_, 2, v_lctx_7147_);
                crate::leanh::lean_ctor_set(v___x_7165_, 3, v_localInstances_7148_);
                crate::leanh::lean_ctor_set(v___x_7165_, 4, v_defEqCtx_x3f_7149_);
                crate::leanh::lean_ctor_set(v___x_7165_, 5, v_synthPendingDepth_7150_);
                crate::leanh::lean_ctor_set(v___x_7165_, 6, v_canUnfold_x3f_7151_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_7145_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7152_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7153_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7154_,
                );
                crate::leanh::lean_inc(v_a_7121_);
                crate::leanh::lean_inc_ref(v_a_7120_);
                crate::leanh::lean_inc(v_a_7119_);
                v___x_7166_ = lean_whnf(v_type_7117_, v___x_7165_, v_a_7119_, v_a_7120_, v_a_7121_);
                if crate::leanh::lean_obj_tag(v___x_7166_) == 0 {
                    v_a_7167_ = crate::leanh::lean_ctor_get(v___x_7166_, 0);
                    v_isSharedCheck_7196_ = (!crate::leanh::lean_is_exclusive(v___x_7166_)) as u8;
                    if v_isSharedCheck_7196_ == 0 {
                        v___x_7169_ = v___x_7166_;
                        v_isShared_7170_ = v_isSharedCheck_7196_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7167_);
                        crate::leanh::lean_dec(v___x_7166_);
                        v___x_7169_ = crate::leanh::lean_box(0);
                        v_isShared_7170_ = v_isSharedCheck_7196_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_7197_ = crate::leanh::lean_ctor_get(v___x_7166_, 0);
                    v_isSharedCheck_7204_ = (!crate::leanh::lean_is_exclusive(v___x_7166_)) as u8;
                    if v_isSharedCheck_7204_ == 0 {
                        v___x_7199_ = v___x_7166_;
                        v_isShared_7200_ = v_isSharedCheck_7204_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7197_);
                        crate::leanh::lean_dec(v___x_7166_);
                        v___x_7199_ = crate::leanh::lean_box(0);
                        v_isShared_7200_ = v_isSharedCheck_7204_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_7167_) == 5 {
                    crate::leanh::lean_del_object(v___x_7169_);
                    v_fn_7171_ = crate::leanh::lean_ctor_get(v_a_7167_, 0);
                    crate::leanh::lean_inc_ref(v_fn_7171_);
                    v_arg_7172_ = crate::leanh::lean_ctor_get(v_a_7167_, 1);
                    crate::leanh::lean_inc_ref(v_arg_7172_);
                    crate::leanh::lean_dec_ref_known(v_a_7167_, 2);
                    v___x_7173_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
                            v_fn_7171_, v_a_7119_,
                        );
                    v_a_7174_ = crate::leanh::lean_ctor_get(v___x_7173_, 0);
                    v_isSharedCheck_7191_ = (!crate::leanh::lean_is_exclusive(v___x_7173_)) as u8;
                    if v_isSharedCheck_7191_ == 0 {
                        v___x_7176_ = v___x_7173_;
                        v_isShared_7177_ = v_isSharedCheck_7191_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7174_);
                        crate::leanh::lean_dec(v___x_7173_);
                        v___x_7176_ = crate::leanh::lean_box(0);
                        v_isShared_7177_ = v_isSharedCheck_7191_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7167_);
                    v___x_7192_ = crate::leanh::lean_box(0);
                    if v_isShared_7170_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7169_, 0, v___x_7192_);
                        v___x_7194_ = v___x_7169_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7195_, 0, v___x_7192_);
                        v___x_7194_ = v_reuseFailAlloc_7195_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7178_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
                        v_arg_7172_,
                        v_a_7119_,
                    );
                v_a_7179_ = crate::leanh::lean_ctor_get(v___x_7178_, 0);
                v_isSharedCheck_7190_ = (!crate::leanh::lean_is_exclusive(v___x_7178_)) as u8;
                if v_isSharedCheck_7190_ == 0 {
                    v___x_7181_ = v___x_7178_;
                    v_isShared_7182_ = v_isSharedCheck_7190_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7179_);
                    crate::leanh::lean_dec(v___x_7178_);
                    v___x_7181_ = crate::leanh::lean_box(0);
                    v_isShared_7182_ = v_isSharedCheck_7190_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7183_, 0, v_a_7174_);
                crate::leanh::lean_ctor_set(v___x_7183_, 1, v_a_7179_);
                if v_isShared_7177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7176_, 1);
                    crate::leanh::lean_ctor_set(v___x_7176_, 0, v___x_7183_);
                    v___x_7185_ = v___x_7176_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7189_, 0, v___x_7183_);
                    v___x_7185_ = v_reuseFailAlloc_7189_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7181_, 0, v___x_7185_);
                    v___x_7187_ = v___x_7181_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7188_, 0, v___x_7185_);
                    v___x_7187_ = v_reuseFailAlloc_7188_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7187_;
            }
            8 => {
                return v___x_7194_;
            }
            9 => {
                if v_isShared_7200_ == 0 {
                    v___x_7202_ = v___x_7199_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7203_, 0, v_a_7197_);
                    v___x_7202_ = v_reuseFailAlloc_7203_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isTypeApp_x3f___boxed(
    mut v_type_7207_: *mut crate::leanh::LeanObject,
    mut v_a_7208_: *mut crate::leanh::LeanObject,
    mut v_a_7209_: *mut crate::leanh::LeanObject,
    mut v_a_7210_: *mut crate::leanh::LeanObject,
    mut v_a_7211_: *mut crate::leanh::LeanObject,
    mut v_a_7212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7213_ =
        l_Lean_Meta_isTypeApp_x3f(v_type_7207_, v_a_7208_, v_a_7209_, v_a_7210_, v_a_7211_);
    crate::leanh::lean_dec(v_a_7211_);
    crate::leanh::lean_dec_ref(v_a_7210_);
    crate::leanh::lean_dec(v_a_7209_);
    crate::leanh::lean_dec_ref(v_a_7208_);
    return v_res_7213_;
}
pub unsafe fn l_Lean_Meta_isMonadApp(
    mut v_type_7214_: *mut crate::leanh::LeanObject,
    mut v_a_7215_: *mut crate::leanh::LeanObject,
    mut v_a_7216_: *mut crate::leanh::LeanObject,
    mut v_a_7217_: *mut crate::leanh::LeanObject,
    mut v_a_7218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7224_: u8 = 0;
    let mut v_val_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7231_: u8 = 0;
    let mut v___x_7232_: u8 = 0;
    let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: u8 = 0;
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7242_: u8 = 0;
    let mut v_a_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7246_: u8 = 0;
    let mut v___x_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7250_: u8 = 0;
    let mut v___x_7251_: u8 = 0;
    let mut v___x_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7256_: u8 = 0;
    let mut v_a_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7260_: u8 = 0;
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7220_ = l_Lean_Meta_isTypeApp_x3f(
                    v_type_7214_,
                    v_a_7215_,
                    v_a_7216_,
                    v_a_7217_,
                    v_a_7218_,
                );
                if crate::leanh::lean_obj_tag(v___x_7220_) == 0 {
                    v_a_7221_ = crate::leanh::lean_ctor_get(v___x_7220_, 0);
                    v_isSharedCheck_7256_ = (!crate::leanh::lean_is_exclusive(v___x_7220_)) as u8;
                    if v_isSharedCheck_7256_ == 0 {
                        v___x_7223_ = v___x_7220_;
                        v_isShared_7224_ = v_isSharedCheck_7256_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7221_);
                        crate::leanh::lean_dec(v___x_7220_);
                        v___x_7223_ = crate::leanh::lean_box(0);
                        v_isShared_7224_ = v_isSharedCheck_7256_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7257_ = crate::leanh::lean_ctor_get(v___x_7220_, 0);
                    v_isSharedCheck_7264_ = (!crate::leanh::lean_is_exclusive(v___x_7220_)) as u8;
                    if v_isSharedCheck_7264_ == 0 {
                        v___x_7259_ = v___x_7220_;
                        v_isShared_7260_ = v_isSharedCheck_7264_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7257_);
                        crate::leanh::lean_dec(v___x_7220_);
                        v___x_7259_ = crate::leanh::lean_box(0);
                        v_isShared_7260_ = v_isSharedCheck_7264_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7221_) == 1 {
                    crate::leanh::lean_del_object(v___x_7223_);
                    v_val_7225_ = crate::leanh::lean_ctor_get(v_a_7221_, 0);
                    crate::leanh::lean_inc(v_val_7225_);
                    crate::leanh::lean_dec_ref_known(v_a_7221_, 1);
                    v_fst_7226_ = crate::leanh::lean_ctor_get(v_val_7225_, 0);
                    crate::leanh::lean_inc(v_fst_7226_);
                    crate::leanh::lean_dec(v_val_7225_);
                    v___x_7227_ = l_Lean_Meta_isMonad_x3f(
                        v_fst_7226_,
                        v_a_7215_,
                        v_a_7216_,
                        v_a_7217_,
                        v_a_7218_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7227_) == 0 {
                        v_a_7228_ = crate::leanh::lean_ctor_get(v___x_7227_, 0);
                        v_isSharedCheck_7242_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7227_)) as u8;
                        if v_isSharedCheck_7242_ == 0 {
                            v___x_7230_ = v___x_7227_;
                            v_isShared_7231_ = v_isSharedCheck_7242_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7228_);
                            crate::leanh::lean_dec(v___x_7227_);
                            v___x_7230_ = crate::leanh::lean_box(0);
                            v_isShared_7231_ = v_isSharedCheck_7242_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_7243_ = crate::leanh::lean_ctor_get(v___x_7227_, 0);
                        v_isSharedCheck_7250_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7227_)) as u8;
                        if v_isSharedCheck_7250_ == 0 {
                            v___x_7245_ = v___x_7227_;
                            v_isShared_7246_ = v_isSharedCheck_7250_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7243_);
                            crate::leanh::lean_dec(v___x_7227_);
                            v___x_7245_ = crate::leanh::lean_box(0);
                            v_isShared_7246_ = v_isSharedCheck_7250_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7221_);
                    v___x_7251_ = 0;
                    v___x_7252_ = crate::leanh::lean_box((v___x_7251_) as usize);
                    if v_isShared_7224_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7223_, 0, v___x_7252_);
                        v___x_7254_ = v___x_7223_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7255_, 0, v___x_7252_);
                        v___x_7254_ = v_reuseFailAlloc_7255_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7228_) == 0 {
                    v___x_7232_ = 0;
                    v___x_7233_ = crate::leanh::lean_box((v___x_7232_) as usize);
                    if v_isShared_7231_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7230_, 0, v___x_7233_);
                        v___x_7235_ = v___x_7230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7236_, 0, v___x_7233_);
                        v___x_7235_ = v_reuseFailAlloc_7236_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_7228_, 1);
                    v___x_7237_ = 1;
                    v___x_7238_ = crate::leanh::lean_box((v___x_7237_) as usize);
                    if v_isShared_7231_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7230_, 0, v___x_7238_);
                        v___x_7240_ = v___x_7230_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7241_, 0, v___x_7238_);
                        v___x_7240_ = v_reuseFailAlloc_7241_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_7235_;
            }
            4 => {
                return v___x_7240_;
            }
            5 => {
                if v_isShared_7246_ == 0 {
                    v___x_7248_ = v___x_7245_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7249_, 0, v_a_7243_);
                    v___x_7248_ = v_reuseFailAlloc_7249_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7248_;
            }
            7 => {
                return v___x_7254_;
            }
            8 => {
                if v_isShared_7260_ == 0 {
                    v___x_7262_ = v___x_7259_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7263_, 0, v_a_7257_);
                    v___x_7262_ = v_reuseFailAlloc_7263_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isMonadApp___boxed(
    mut v_type_7265_: *mut crate::leanh::LeanObject,
    mut v_a_7266_: *mut crate::leanh::LeanObject,
    mut v_a_7267_: *mut crate::leanh::LeanObject,
    mut v_a_7268_: *mut crate::leanh::LeanObject,
    mut v_a_7269_: *mut crate::leanh::LeanObject,
    mut v_a_7270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7271_ = l_Lean_Meta_isMonadApp(v_type_7265_, v_a_7266_, v_a_7267_, v_a_7268_, v_a_7269_);
    crate::leanh::lean_dec(v_a_7269_);
    crate::leanh::lean_dec_ref(v_a_7268_);
    crate::leanh::lean_dec(v_a_7267_);
    crate::leanh::lean_dec_ref(v_a_7266_);
    return v_res_7271_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(
    mut v_opts_7272_: *mut crate::leanh::LeanObject,
    mut v_opt_7273_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_7274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_7274_ = crate::leanh::lean_ctor_get(v_opt_7273_, 0);
    v_defValue_7275_ = crate::leanh::lean_ctor_get(v_opt_7273_, 1);
    v_map_7276_ = crate::leanh::lean_ctor_get(v_opts_7272_, 0);
    v___x_7277_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_7276_,
            v_name_7274_,
        );
    if crate::leanh::lean_obj_tag(v___x_7277_) == 0 {
        let mut v___x_7278_: u8 = 0;
        v___x_7278_ = (crate::leanh::lean_unbox(v_defValue_7275_) as u8);
        return v___x_7278_;
    } else {
        let mut v_val_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7279_ = crate::leanh::lean_ctor_get(v___x_7277_, 0);
        crate::leanh::lean_inc(v_val_7279_);
        crate::leanh::lean_dec_ref_known(v___x_7277_, 1);
        if crate::leanh::lean_obj_tag(v_val_7279_) == 1 {
            let mut v_v_7280_: u8 = 0;
            v_v_7280_ = crate::leanh::lean_ctor_get_uint8(v_val_7279_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_7279_, 0);
            return v_v_7280_;
        } else {
            let mut v___x_7281_: u8 = 0;
            crate::leanh::lean_dec(v_val_7279_);
            v___x_7281_ = (crate::leanh::lean_unbox(v_defValue_7275_) as u8);
            return v___x_7281_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0___boxed(
    mut v_opts_7282_: *mut crate::leanh::LeanObject,
    mut v_opt_7283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7284_: u8 = 0;
    let mut v_r_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7284_ =
        l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(v_opts_7282_, v_opt_7283_);
    crate::leanh::lean_dec_ref(v_opt_7283_);
    crate::leanh::lean_dec_ref(v_opts_7282_);
    v_r_7285_ = crate::leanh::lean_box((v_res_7284_) as usize);
    return v_r_7285_;
}
pub unsafe fn l_Lean_Meta_coerceMonadLift_x3f___lam__0(
    mut v_x_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
    mut v___y_7291_: *mut crate::leanh::LeanObject,
    mut v___y_7292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7294_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0___closed__0;
    v___x_7295_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7295_, 0, v___x_7294_);
    return v___x_7295_;
}
pub unsafe fn l_Lean_Meta_coerceMonadLift_x3f___lam__0___boxed(
    mut v_x_7296_: *mut crate::leanh::LeanObject,
    mut v___y_7297_: *mut crate::leanh::LeanObject,
    mut v___y_7298_: *mut crate::leanh::LeanObject,
    mut v___y_7299_: *mut crate::leanh::LeanObject,
    mut v___y_7300_: *mut crate::leanh::LeanObject,
    mut v___y_7301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7302_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(
        v_x_7296_,
        v___y_7297_,
        v___y_7298_,
        v___y_7299_,
        v___y_7300_,
    );
    crate::leanh::lean_dec(v___y_7300_);
    crate::leanh::lean_dec_ref(v___y_7299_);
    crate::leanh::lean_dec(v___y_7298_);
    crate::leanh::lean_dec_ref(v___y_7297_);
    crate::leanh::lean_dec_ref(v_x_7296_);
    return v_res_7302_;
}
pub unsafe fn _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7312_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7313_ = l_Lean_mkBVar(v___x_7312_);
    return v___x_7313_;
}
pub unsafe fn l_Lean_Meta_coerceMonadLift_x3f(
    mut v_e_7325_: *mut crate::leanh::LeanObject,
    mut v_expectedType_7326_: *mut crate::leanh::LeanObject,
    mut v_a_7327_: *mut crate::leanh::LeanObject,
    mut v_a_7328_: *mut crate::leanh::LeanObject,
    mut v_a_7329_: *mut crate::leanh::LeanObject,
    mut v_a_7330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7334_: u8 = 0;
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: u8 = 0;
    let mut v___x_7341_: u8 = 0;
    let mut v___y_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7347_: u8 = 0;
    let mut v_a_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7352_: u8 = 0;
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7357_: u8 = 0;
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7364_: u8 = 0;
    let mut v___x_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7369_: u8 = 0;
    let mut v_val_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7373_: u8 = 0;
    let mut v_fst_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7378_: u8 = 0;
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7383_: u8 = 0;
    let mut v_val_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7387_: u8 = 0;
    let mut v_fst_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7392_: u8 = 0;
    let mut v___x_7393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7399_: u8 = 0;
    let mut v___x_7400_: u8 = 0;
    let mut v_options_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: u8 = 0;
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_7423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7432_: u8 = 0;
    let mut v___x_7433_: u8 = 0;
    let mut v___x_7434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7456_: u8 = 0;
    let mut v_a_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7483_: u8 = 0;
    let mut v___x_7484_: u8 = 0;
    let mut v___x_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7489_: u8 = 0;
    let mut v_val_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7493_: u8 = 0;
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: u8 = 0;
    let mut v___x_7500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7516_: u8 = 0;
    let mut v_a_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7540_: u8 = 0;
    let mut v___x_7541_: u8 = 0;
    let mut v___x_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7551_: u8 = 0;
    let mut v_a_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7558_: u8 = 0;
    let mut v_a_7559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7562_: u8 = 0;
    let mut v___x_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7566_: u8 = 0;
    let mut v_a_7567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7574_: u8 = 0;
    let mut v_a_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7583_: u8 = 0;
    let mut v_a_7584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7593_: u8 = 0;
    let mut v_a_7594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7611_: u8 = 0;
    let mut v___x_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7622_: u8 = 0;
    let mut v___x_7623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7626_: u8 = 0;
    let mut v___x_7628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7630_: u8 = 0;
    let mut v_unused_7631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7635_: u8 = 0;
    let mut v___x_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7639_: u8 = 0;
    let mut v___x_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: u8 = 0;
    let mut v___x_7646_: u8 = 0;
    let mut v___x_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7661_: u8 = 0;
    let mut v___x_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7666_: u8 = 0;
    let mut v_fst_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7674_: u8 = 0;
    let mut v_a_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7676_: u8 = 0;
    let mut v_a_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7685_: u8 = 0;
    let mut v___x_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7690_: u8 = 0;
    let mut v_unused_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7695_: u8 = 0;
    let mut v___x_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7699_: u8 = 0;
    let mut v_isSharedCheck_7700_: u8 = 0;
    let mut v_isSharedCheck_7701_: u8 = 0;
    let mut v_a_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7705_: u8 = 0;
    let mut v___x_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7709_: u8 = 0;
    let mut v_a_7710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7713_: u8 = 0;
    let mut v___x_7715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut v_isSharedCheck_7718_: u8 = 0;
    let mut v_isSharedCheck_7719_: u8 = 0;
    let mut v___x_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7724_: u8 = 0;
    let mut v_a_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7728_: u8 = 0;
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7732_: u8 = 0;
    let mut v_isSharedCheck_7733_: u8 = 0;
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v___x_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7739_: u8 = 0;
    let mut v_a_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7743_: u8 = 0;
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7747_: u8 = 0;
    let mut v_isSharedCheck_7748_: u8 = 0;
    let mut v_a_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7752_: u8 = 0;
    let mut v___x_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7756_: u8 = 0;
    let mut v_isSharedCheck_7757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7353_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
                        v_expectedType_7326_,
                        v_a_7328_,
                    );
                v_a_7354_ = crate::leanh::lean_ctor_get(v___x_7353_, 0);
                v_isSharedCheck_7757_ = (!crate::leanh::lean_is_exclusive(v___x_7353_)) as u8;
                if v_isSharedCheck_7757_ == 0 {
                    v___x_7356_ = v___x_7353_;
                    v_isShared_7357_ = v_isSharedCheck_7757_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7354_);
                    crate::leanh::lean_dec(v___x_7353_);
                    v___x_7356_ = crate::leanh::lean_box(0);
                    v_isShared_7357_ = v_isSharedCheck_7757_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if v___y_7334_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_7333_);
                    v___x_7335_ = crate::leanh::lean_box(0);
                    v___x_7336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7336_, 0, v___x_7335_);
                    return v___x_7336_;
                } else {
                    v___x_7337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7337_, 0, v___y_7333_);
                    return v___x_7337_;
                }
            }
            2 => {
                v___x_7340_ = l_Lean_Exception_isInterrupt(v_a_7339_);
                if v___x_7340_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_7339_);
                    v___x_7341_ = l_Lean_Exception_isRuntime(v_a_7339_);
                    v___y_7333_ = v_a_7339_;
                    v___y_7334_ = v___x_7341_;
                    state = 1;
                    continue;
                } else {
                    v___y_7333_ = v_a_7339_;
                    v___y_7334_ = v___x_7340_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_7344_ = crate::leanh::lean_ctor_get(v___y_7343_, 0);
                v_isSharedCheck_7352_ = (!crate::leanh::lean_is_exclusive(v___y_7343_)) as u8;
                if v_isSharedCheck_7352_ == 0 {
                    v___x_7346_ = v___y_7343_;
                    v_isShared_7347_ = v_isSharedCheck_7352_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7344_);
                    crate::leanh::lean_dec(v___y_7343_);
                    v___x_7346_ = crate::leanh::lean_box(0);
                    v_isShared_7347_ = v_isSharedCheck_7352_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_7348_ = crate::leanh::lean_ctor_get(v_a_7344_, 0);
                crate::leanh::lean_inc(v_a_7348_);
                crate::leanh::lean_dec(v_a_7344_);
                if v_isShared_7347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7346_, 0, v_a_7348_);
                    v___x_7350_ = v___x_7346_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 0, v_a_7348_);
                    v___x_7350_ = v_reuseFailAlloc_7351_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7350_;
            }
            6 => {
                crate::leanh::lean_inc(v_a_7330_);
                crate::leanh::lean_inc_ref(v_a_7329_);
                crate::leanh::lean_inc(v_a_7328_);
                crate::leanh::lean_inc_ref(v_a_7327_);
                crate::leanh::lean_inc_ref(v_e_7325_);
                v___x_7358_ =
                    lean_infer_type(v_e_7325_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                if crate::leanh::lean_obj_tag(v___x_7358_) == 0 {
                    v_a_7359_ = crate::leanh::lean_ctor_get(v___x_7358_, 0);
                    crate::leanh::lean_inc(v_a_7359_);
                    crate::leanh::lean_dec_ref_known(v___x_7358_, 1);
                    v___x_7360_ =
                        l_Lean_instantiateMVars___at___00Lean_Meta_isTypeApp_x3f_spec__0___redArg(
                            v_a_7359_, v_a_7328_,
                        );
                    v_a_7361_ = crate::leanh::lean_ctor_get(v___x_7360_, 0);
                    v_isSharedCheck_7748_ = (!crate::leanh::lean_is_exclusive(v___x_7360_)) as u8;
                    if v_isSharedCheck_7748_ == 0 {
                        v___x_7363_ = v___x_7360_;
                        v_isShared_7364_ = v_isSharedCheck_7748_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7361_);
                        crate::leanh::lean_dec(v___x_7360_);
                        v___x_7363_ = crate::leanh::lean_box(0);
                        v_isShared_7364_ = v_isSharedCheck_7748_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v_a_7749_ = crate::leanh::lean_ctor_get(v___x_7358_, 0);
                    v_isSharedCheck_7756_ = (!crate::leanh::lean_is_exclusive(v___x_7358_)) as u8;
                    if v_isSharedCheck_7756_ == 0 {
                        v___x_7751_ = v___x_7358_;
                        v_isShared_7752_ = v_isSharedCheck_7756_;
                        state = 64;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7749_);
                        crate::leanh::lean_dec(v___x_7358_);
                        v___x_7751_ = crate::leanh::lean_box(0);
                        v_isShared_7752_ = v_isSharedCheck_7756_;
                        state = 64;
                        continue;
                    }
                }
            }
            7 => {
                crate::leanh::lean_inc(v_a_7354_);
                v___x_7365_ = l_Lean_Meta_isTypeApp_x3f(
                    v_a_7354_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                );
                if crate::leanh::lean_obj_tag(v___x_7365_) == 0 {
                    v_a_7366_ = crate::leanh::lean_ctor_get(v___x_7365_, 0);
                    v_isSharedCheck_7739_ = (!crate::leanh::lean_is_exclusive(v___x_7365_)) as u8;
                    if v_isSharedCheck_7739_ == 0 {
                        v___x_7368_ = v___x_7365_;
                        v_isShared_7369_ = v_isSharedCheck_7739_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7366_);
                        crate::leanh::lean_dec(v___x_7365_);
                        v___x_7368_ = crate::leanh::lean_box(0);
                        v_isShared_7369_ = v_isSharedCheck_7739_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v_a_7740_ = crate::leanh::lean_ctor_get(v___x_7365_, 0);
                    v_isSharedCheck_7747_ = (!crate::leanh::lean_is_exclusive(v___x_7365_)) as u8;
                    if v_isSharedCheck_7747_ == 0 {
                        v___x_7742_ = v___x_7365_;
                        v_isShared_7743_ = v_isSharedCheck_7747_;
                        state = 62;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7740_);
                        crate::leanh::lean_dec(v___x_7365_);
                        v___x_7742_ = crate::leanh::lean_box(0);
                        v_isShared_7743_ = v_isSharedCheck_7747_;
                        state = 62;
                        continue;
                    }
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_7366_) == 1 {
                    crate::leanh::lean_del_object(v___x_7368_);
                    v_val_7370_ = crate::leanh::lean_ctor_get(v_a_7366_, 0);
                    v_isSharedCheck_7734_ = (!crate::leanh::lean_is_exclusive(v_a_7366_)) as u8;
                    if v_isSharedCheck_7734_ == 0 {
                        v___x_7372_ = v_a_7366_;
                        v_isShared_7373_ = v_isSharedCheck_7734_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7370_);
                        crate::leanh::lean_dec(v_a_7366_);
                        v___x_7372_ = crate::leanh::lean_box(0);
                        v_isShared_7373_ = v_isSharedCheck_7734_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7366_);
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v___x_7735_ = crate::leanh::lean_box(0);
                    if v_isShared_7369_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7368_, 0, v___x_7735_);
                        v___x_7737_ = v___x_7368_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_7738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7738_, 0, v___x_7735_);
                        v___x_7737_ = v_reuseFailAlloc_7738_;
                        state = 61;
                        continue;
                    }
                }
            }
            9 => {
                v_fst_7374_ = crate::leanh::lean_ctor_get(v_val_7370_, 0);
                v_snd_7375_ = crate::leanh::lean_ctor_get(v_val_7370_, 1);
                v_isSharedCheck_7733_ = (!crate::leanh::lean_is_exclusive(v_val_7370_)) as u8;
                if v_isSharedCheck_7733_ == 0 {
                    v___x_7377_ = v_val_7370_;
                    v_isShared_7378_ = v_isSharedCheck_7733_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7375_);
                    crate::leanh::lean_inc(v_fst_7374_);
                    crate::leanh::lean_dec(v_val_7370_);
                    v___x_7377_ = crate::leanh::lean_box(0);
                    v_isShared_7378_ = v_isSharedCheck_7733_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc(v_a_7361_);
                v___x_7379_ = l_Lean_Meta_isTypeApp_x3f(
                    v_a_7361_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                );
                if crate::leanh::lean_obj_tag(v___x_7379_) == 0 {
                    v_a_7380_ = crate::leanh::lean_ctor_get(v___x_7379_, 0);
                    v_isSharedCheck_7724_ = (!crate::leanh::lean_is_exclusive(v___x_7379_)) as u8;
                    if v_isSharedCheck_7724_ == 0 {
                        v___x_7382_ = v___x_7379_;
                        v_isShared_7383_ = v_isSharedCheck_7724_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7380_);
                        crate::leanh::lean_dec(v___x_7379_);
                        v___x_7382_ = crate::leanh::lean_box(0);
                        v_isShared_7383_ = v_isSharedCheck_7724_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7377_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_del_object(v___x_7372_);
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v_a_7725_ = crate::leanh::lean_ctor_get(v___x_7379_, 0);
                    v_isSharedCheck_7732_ = (!crate::leanh::lean_is_exclusive(v___x_7379_)) as u8;
                    if v_isSharedCheck_7732_ == 0 {
                        v___x_7727_ = v___x_7379_;
                        v_isShared_7728_ = v_isSharedCheck_7732_;
                        state = 59;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7725_);
                        crate::leanh::lean_dec(v___x_7379_);
                        v___x_7727_ = crate::leanh::lean_box(0);
                        v_isShared_7728_ = v_isSharedCheck_7732_;
                        state = 59;
                        continue;
                    }
                }
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_a_7380_) == 1 {
                    crate::leanh::lean_del_object(v___x_7382_);
                    v_val_7384_ = crate::leanh::lean_ctor_get(v_a_7380_, 0);
                    v_isSharedCheck_7719_ = (!crate::leanh::lean_is_exclusive(v_a_7380_)) as u8;
                    if v_isSharedCheck_7719_ == 0 {
                        v___x_7386_ = v_a_7380_;
                        v_isShared_7387_ = v_isSharedCheck_7719_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7384_);
                        crate::leanh::lean_dec(v_a_7380_);
                        v___x_7386_ = crate::leanh::lean_box(0);
                        v_isShared_7387_ = v_isSharedCheck_7719_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7380_);
                    crate::leanh::lean_del_object(v___x_7377_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_del_object(v___x_7372_);
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v___x_7720_ = crate::leanh::lean_box(0);
                    if v_isShared_7383_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7382_, 0, v___x_7720_);
                        v___x_7722_ = v___x_7382_;
                        state = 58;
                        continue;
                    } else {
                        v_reuseFailAlloc_7723_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7723_, 0, v___x_7720_);
                        v___x_7722_ = v_reuseFailAlloc_7723_;
                        state = 58;
                        continue;
                    }
                }
            }
            12 => {
                v_fst_7388_ = crate::leanh::lean_ctor_get(v_val_7384_, 0);
                v_snd_7389_ = crate::leanh::lean_ctor_get(v_val_7384_, 1);
                v_isSharedCheck_7718_ = (!crate::leanh::lean_is_exclusive(v_val_7384_)) as u8;
                if v_isSharedCheck_7718_ == 0 {
                    v___x_7391_ = v_val_7384_;
                    v_isShared_7392_ = v_isSharedCheck_7718_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7389_);
                    crate::leanh::lean_inc(v_fst_7388_);
                    crate::leanh::lean_dec(v_val_7384_);
                    v___x_7391_ = crate::leanh::lean_box(0);
                    v_isShared_7392_ = v_isSharedCheck_7718_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_7393_ = l_Lean_Meta_saveState___redArg(v_a_7328_, v_a_7330_);
                if crate::leanh::lean_obj_tag(v___x_7393_) == 0 {
                    v_a_7394_ = crate::leanh::lean_ctor_get(v___x_7393_, 0);
                    crate::leanh::lean_inc(v_a_7394_);
                    crate::leanh::lean_dec_ref_known(v___x_7393_, 1);
                    crate::leanh::lean_inc(v_fst_7374_);
                    crate::leanh::lean_inc(v_fst_7388_);
                    v___x_7395_ = l_Lean_Meta_isExprDefEq(
                        v_fst_7388_,
                        v_fst_7374_,
                        v_a_7327_,
                        v_a_7328_,
                        v_a_7329_,
                        v_a_7330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7395_) == 0 {
                        v_a_7396_ = crate::leanh::lean_ctor_get(v___x_7395_, 0);
                        v_isSharedCheck_7701_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7395_)) as u8;
                        if v_isSharedCheck_7701_ == 0 {
                            v___x_7398_ = v___x_7395_;
                            v_isShared_7399_ = v_isSharedCheck_7701_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7396_);
                            crate::leanh::lean_dec(v___x_7395_);
                            v___x_7398_ = crate::leanh::lean_box(0);
                            v_isShared_7399_ = v_isSharedCheck_7701_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7394_);
                        crate::leanh::lean_del_object(v___x_7391_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_del_object(v___x_7386_);
                        crate::leanh::lean_del_object(v___x_7377_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_dec(v_fst_7374_);
                        crate::leanh::lean_del_object(v___x_7372_);
                        crate::leanh::lean_del_object(v___x_7363_);
                        crate::leanh::lean_dec(v_a_7361_);
                        crate::leanh::lean_del_object(v___x_7356_);
                        crate::leanh::lean_dec(v_a_7354_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        v_a_7702_ = crate::leanh::lean_ctor_get(v___x_7395_, 0);
                        v_isSharedCheck_7709_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7395_)) as u8;
                        if v_isSharedCheck_7709_ == 0 {
                            v___x_7704_ = v___x_7395_;
                            v_isShared_7705_ = v_isSharedCheck_7709_;
                            state = 54;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7702_);
                            crate::leanh::lean_dec(v___x_7395_);
                            v___x_7704_ = crate::leanh::lean_box(0);
                            v_isShared_7705_ = v_isSharedCheck_7709_;
                            state = 54;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7391_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_del_object(v___x_7386_);
                    crate::leanh::lean_del_object(v___x_7377_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_del_object(v___x_7372_);
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v_a_7710_ = crate::leanh::lean_ctor_get(v___x_7393_, 0);
                    v_isSharedCheck_7717_ = (!crate::leanh::lean_is_exclusive(v___x_7393_)) as u8;
                    if v_isSharedCheck_7717_ == 0 {
                        v___x_7712_ = v___x_7393_;
                        v_isShared_7713_ = v_isSharedCheck_7717_;
                        state = 56;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7710_);
                        crate::leanh::lean_dec(v___x_7393_);
                        v___x_7712_ = crate::leanh::lean_box(0);
                        v_isShared_7713_ = v_isSharedCheck_7717_;
                        state = 56;
                        continue;
                    }
                }
            }
            14 => {
                v___x_7400_ = (crate::leanh::lean_unbox(v_a_7396_) as u8);
                crate::leanh::lean_dec(v_a_7396_);
                if v___x_7400_ == 0 {
                    crate::leanh::lean_dec(v_a_7394_);
                    crate::leanh::lean_del_object(v___x_7372_);
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    v_options_7401_ = crate::leanh::lean_ctor_get(v_a_7329_, 2);
                    v___x_7402_ = l_Lean_Meta_autoLift;
                    v___x_7403_ = l_Lean_Option_get___at___00Lean_Meta_coerceMonadLift_x3f_spec__0(
                        v_options_7401_,
                        v___x_7402_,
                    );
                    if v___x_7403_ == 0 {
                        crate::leanh::lean_del_object(v___x_7391_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_del_object(v___x_7386_);
                        crate::leanh::lean_del_object(v___x_7377_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_dec(v_fst_7374_);
                        crate::leanh::lean_dec(v_a_7361_);
                        crate::leanh::lean_dec(v_a_7354_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        v___x_7404_ = crate::leanh::lean_box(0);
                        if v_isShared_7399_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7398_, 0, v___x_7404_);
                            v___x_7406_ = v___x_7398_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_7407_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7407_, 0, v___x_7404_);
                            v___x_7406_ = v_reuseFailAlloc_7407_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_7398_);
                        crate::leanh::lean_inc(v_a_7330_);
                        crate::leanh::lean_inc_ref(v_a_7329_);
                        crate::leanh::lean_inc(v_a_7328_);
                        crate::leanh::lean_inc_ref(v_a_7327_);
                        crate::leanh::lean_inc(v_fst_7388_);
                        v___x_7408_ = lean_infer_type(
                            v_fst_7388_,
                            v_a_7327_,
                            v_a_7328_,
                            v_a_7329_,
                            v_a_7330_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7408_) == 0 {
                            v_a_7409_ = crate::leanh::lean_ctor_get(v___x_7408_, 0);
                            crate::leanh::lean_inc(v_a_7409_);
                            crate::leanh::lean_dec_ref_known(v___x_7408_, 1);
                            crate::leanh::lean_inc(v_a_7330_);
                            crate::leanh::lean_inc_ref(v_a_7329_);
                            crate::leanh::lean_inc(v_a_7328_);
                            crate::leanh::lean_inc_ref(v_a_7327_);
                            v___x_7410_ =
                                lean_whnf(v_a_7409_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                            if crate::leanh::lean_obj_tag(v___x_7410_) == 0 {
                                v_a_7411_ = crate::leanh::lean_ctor_get(v___x_7410_, 0);
                                crate::leanh::lean_inc(v_a_7411_);
                                crate::leanh::lean_dec_ref_known(v___x_7410_, 1);
                                if crate::leanh::lean_obj_tag(v_a_7411_) == 7 {
                                    v_binderType_7412_ = crate::leanh::lean_ctor_get(v_a_7411_, 1);
                                    if crate::leanh::lean_obj_tag(v_binderType_7412_) == 3 {
                                        v_body_7413_ = crate::leanh::lean_ctor_get(v_a_7411_, 2);
                                        if crate::leanh::lean_obj_tag(v_body_7413_) == 3 {
                                            crate::leanh::lean_inc_ref(v_body_7413_);
                                            crate::leanh::lean_inc_ref(v_binderType_7412_);
                                            crate::leanh::lean_dec_ref_known(v_a_7411_, 3);
                                            v_u_7414_ =
                                                crate::leanh::lean_ctor_get(v_binderType_7412_, 0);
                                            crate::leanh::lean_inc(v_u_7414_);
                                            crate::leanh::lean_dec_ref_known(v_binderType_7412_, 1);
                                            v_u_7415_ =
                                                crate::leanh::lean_ctor_get(v_body_7413_, 0);
                                            crate::leanh::lean_inc(v_u_7415_);
                                            crate::leanh::lean_dec_ref_known(v_body_7413_, 1);
                                            crate::leanh::lean_inc(v_a_7330_);
                                            crate::leanh::lean_inc_ref(v_a_7329_);
                                            crate::leanh::lean_inc(v_a_7328_);
                                            crate::leanh::lean_inc_ref(v_a_7327_);
                                            crate::leanh::lean_inc(v_fst_7374_);
                                            v___x_7416_ = lean_infer_type(
                                                v_fst_7374_,
                                                v_a_7327_,
                                                v_a_7328_,
                                                v_a_7329_,
                                                v_a_7330_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_7416_) == 0 {
                                                v_a_7417_ =
                                                    crate::leanh::lean_ctor_get(v___x_7416_, 0);
                                                crate::leanh::lean_inc(v_a_7417_);
                                                crate::leanh::lean_dec_ref_known(v___x_7416_, 1);
                                                crate::leanh::lean_inc(v_a_7330_);
                                                crate::leanh::lean_inc_ref(v_a_7329_);
                                                crate::leanh::lean_inc(v_a_7328_);
                                                crate::leanh::lean_inc_ref(v_a_7327_);
                                                v___x_7418_ = lean_whnf(
                                                    v_a_7417_, v_a_7327_, v_a_7328_, v_a_7329_,
                                                    v_a_7330_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_7418_) == 0 {
                                                    v_a_7419_ =
                                                        crate::leanh::lean_ctor_get(v___x_7418_, 0);
                                                    crate::leanh::lean_inc(v_a_7419_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_7418_,
                                                        1,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v_a_7419_) == 7 {
                                                        v_binderType_7420_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_7419_, 1,
                                                            );
                                                        if crate::leanh::lean_obj_tag(
                                                            v_binderType_7420_,
                                                        ) == 3
                                                        {
                                                            v_body_7421_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_a_7419_, 2,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v_body_7421_,
                                                            ) == 3
                                                            {
                                                                crate::leanh::lean_inc_ref(
                                                                    v_body_7421_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_binderType_7420_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_a_7419_, 3,
                                                                );
                                                                v_u_7422_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_binderType_7420_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_u_7422_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_binderType_7420_,
                                                                    1,
                                                                );
                                                                v_u_7423_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_body_7421_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_u_7423_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_body_7421_,
                                                                    1,
                                                                );
                                                                v___x_7424_ = l_Lean_Meta_decLevel(
                                                                    v_u_7414_, v_a_7327_,
                                                                    v_a_7328_, v_a_7329_,
                                                                    v_a_7330_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_7424_,
                                                                ) == 0
                                                                {
                                                                    v_a_7425_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_7424_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_7425_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_7424_, 1);
                                                                    v___x_7426_ =
                                                                        l_Lean_Meta_decLevel(
                                                                            v_u_7422_, v_a_7327_,
                                                                            v_a_7328_, v_a_7329_,
                                                                            v_a_7330_,
                                                                        );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_7426_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_7427_ = crate::leanh::lean_ctor_get(v___x_7426_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_7427_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_7426_, 1);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_7425_,
                                                                        );
                                                                        v___x_7428_ = l_Lean_Meta_isLevelDefEq(v_a_7425_, v_a_7427_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                                                                        if crate::leanh::lean_obj_tag(v___x_7428_) == 0 {
v_a_7429_ = crate::leanh::lean_ctor_get(v___x_7428_, 0);
v_isSharedCheck_7593_ = (!crate::leanh::lean_is_exclusive(v___x_7428_)) as u8;
if v_isSharedCheck_7593_ == 0 {
v___x_7431_ = v___x_7428_;
v_isShared_7432_ = v_isSharedCheck_7593_;
state = 16; continue;
} else {
crate::leanh::lean_inc(v_a_7429_);
crate::leanh::lean_dec(v___x_7428_);
v___x_7431_ = crate::leanh::lean_box(0);
v_isShared_7432_ = v_isSharedCheck_7593_;
state = 16; continue;
}
} else {
crate::leanh::lean_dec(v_a_7425_);
crate::leanh::lean_dec(v_u_7423_);
crate::leanh::lean_dec(v_u_7415_);
crate::leanh::lean_del_object(v___x_7391_);
crate::leanh::lean_dec(v_snd_7389_);
crate::leanh::lean_dec(v_fst_7388_);
crate::leanh::lean_del_object(v___x_7386_);
crate::leanh::lean_del_object(v___x_7377_);
crate::leanh::lean_dec(v_snd_7375_);
crate::leanh::lean_dec(v_fst_7374_);
crate::leanh::lean_dec(v_a_7361_);
crate::leanh::lean_dec(v_a_7354_);
crate::leanh::lean_dec_ref(v_e_7325_);
v_a_7594_ = crate::leanh::lean_ctor_get(v___x_7428_, 0);
crate::leanh::lean_inc(v_a_7594_);
crate::leanh::lean_dec_ref_known(v___x_7428_, 1);
v_a_7339_ = v_a_7594_;
state = 2; continue;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_7425_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_u_7423_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_u_7415_,
                                                                        );
                                                                        crate::leanh::lean_del_object(v___x_7391_);
                                                                        crate::leanh::lean_dec(
                                                                            v_snd_7389_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_fst_7388_,
                                                                        );
                                                                        crate::leanh::lean_del_object(v___x_7386_);
                                                                        crate::leanh::lean_del_object(v___x_7377_);
                                                                        crate::leanh::lean_dec(
                                                                            v_snd_7375_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_fst_7374_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_7361_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_7354_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_7325_,
                                                                        );
                                                                        v_a_7595_ = crate::leanh::lean_ctor_get(v___x_7426_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_7595_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_7426_, 1);
                                                                        v_a_7339_ = v_a_7595_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_u_7423_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_u_7422_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_u_7415_,
                                                                    );
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_7391_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_snd_7389_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_fst_7388_,
                                                                    );
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_7386_,
                                                                    );
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_7377_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_snd_7375_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_fst_7374_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_7361_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_7354_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_7325_,
                                                                    );
                                                                    v_a_7596_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_7424_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_7596_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_7424_, 1);
                                                                    v_a_7339_ = v_a_7596_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_u_7415_);
                                                                crate::leanh::lean_dec(v_u_7414_);
                                                                crate::leanh::lean_del_object(
                                                                    v___x_7391_,
                                                                );
                                                                crate::leanh::lean_dec(v_snd_7389_);
                                                                crate::leanh::lean_dec(v_fst_7388_);
                                                                crate::leanh::lean_del_object(
                                                                    v___x_7386_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_7377_,
                                                                );
                                                                crate::leanh::lean_dec(v_snd_7375_);
                                                                crate::leanh::lean_dec(v_fst_7374_);
                                                                crate::leanh::lean_dec(v_a_7361_);
                                                                crate::leanh::lean_dec(v_a_7354_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_7325_,
                                                                );
                                                                v___x_7597_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_7419_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_a_7419_, 3,
                                                                );
                                                                v___y_7343_ = v___x_7597_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_u_7415_);
                                                            crate::leanh::lean_dec(v_u_7414_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_7391_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_7389_);
                                                            crate::leanh::lean_dec(v_fst_7388_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_7386_,
                                                            );
                                                            crate::leanh::lean_del_object(
                                                                v___x_7377_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_7375_);
                                                            crate::leanh::lean_dec(v_fst_7374_);
                                                            crate::leanh::lean_dec(v_a_7361_);
                                                            crate::leanh::lean_dec(v_a_7354_);
                                                            crate::leanh::lean_dec_ref(v_e_7325_);
                                                            v___x_7598_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_7419_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_a_7419_, 3,
                                                            );
                                                            v___y_7343_ = v___x_7598_;
                                                            state = 3;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_u_7415_);
                                                        crate::leanh::lean_dec(v_u_7414_);
                                                        crate::leanh::lean_del_object(v___x_7391_);
                                                        crate::leanh::lean_dec(v_snd_7389_);
                                                        crate::leanh::lean_dec(v_fst_7388_);
                                                        crate::leanh::lean_del_object(v___x_7386_);
                                                        crate::leanh::lean_del_object(v___x_7377_);
                                                        crate::leanh::lean_dec(v_snd_7375_);
                                                        crate::leanh::lean_dec(v_fst_7374_);
                                                        crate::leanh::lean_dec(v_a_7361_);
                                                        crate::leanh::lean_dec(v_a_7354_);
                                                        crate::leanh::lean_dec_ref(v_e_7325_);
                                                        v___x_7599_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(v_a_7419_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                                                        crate::leanh::lean_dec(v_a_7419_);
                                                        v___y_7343_ = v___x_7599_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_u_7415_);
                                                    crate::leanh::lean_dec(v_u_7414_);
                                                    crate::leanh::lean_del_object(v___x_7391_);
                                                    crate::leanh::lean_dec(v_snd_7389_);
                                                    crate::leanh::lean_dec(v_fst_7388_);
                                                    crate::leanh::lean_del_object(v___x_7386_);
                                                    crate::leanh::lean_del_object(v___x_7377_);
                                                    crate::leanh::lean_dec(v_snd_7375_);
                                                    crate::leanh::lean_dec(v_fst_7374_);
                                                    crate::leanh::lean_dec(v_a_7361_);
                                                    crate::leanh::lean_dec(v_a_7354_);
                                                    crate::leanh::lean_dec_ref(v_e_7325_);
                                                    v_a_7600_ =
                                                        crate::leanh::lean_ctor_get(v___x_7418_, 0);
                                                    crate::leanh::lean_inc(v_a_7600_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_7418_,
                                                        1,
                                                    );
                                                    v_a_7339_ = v_a_7600_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_u_7415_);
                                                crate::leanh::lean_dec(v_u_7414_);
                                                crate::leanh::lean_del_object(v___x_7391_);
                                                crate::leanh::lean_dec(v_snd_7389_);
                                                crate::leanh::lean_dec(v_fst_7388_);
                                                crate::leanh::lean_del_object(v___x_7386_);
                                                crate::leanh::lean_del_object(v___x_7377_);
                                                crate::leanh::lean_dec(v_snd_7375_);
                                                crate::leanh::lean_dec(v_fst_7374_);
                                                crate::leanh::lean_dec(v_a_7361_);
                                                crate::leanh::lean_dec(v_a_7354_);
                                                crate::leanh::lean_dec_ref(v_e_7325_);
                                                v_a_7601_ =
                                                    crate::leanh::lean_ctor_get(v___x_7416_, 0);
                                                crate::leanh::lean_inc(v_a_7601_);
                                                crate::leanh::lean_dec_ref_known(v___x_7416_, 1);
                                                v_a_7339_ = v_a_7601_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_del_object(v___x_7391_);
                                            crate::leanh::lean_dec(v_snd_7389_);
                                            crate::leanh::lean_dec(v_fst_7388_);
                                            crate::leanh::lean_del_object(v___x_7386_);
                                            crate::leanh::lean_del_object(v___x_7377_);
                                            crate::leanh::lean_dec(v_snd_7375_);
                                            crate::leanh::lean_dec(v_fst_7374_);
                                            crate::leanh::lean_dec(v_a_7361_);
                                            crate::leanh::lean_dec(v_a_7354_);
                                            crate::leanh::lean_dec_ref(v_e_7325_);
                                            v___x_7602_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(
                                                v_a_7411_, v_a_7327_, v_a_7328_, v_a_7329_,
                                                v_a_7330_,
                                            );
                                            crate::leanh::lean_dec_ref_known(v_a_7411_, 3);
                                            v___y_7343_ = v___x_7602_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_del_object(v___x_7391_);
                                        crate::leanh::lean_dec(v_snd_7389_);
                                        crate::leanh::lean_dec(v_fst_7388_);
                                        crate::leanh::lean_del_object(v___x_7386_);
                                        crate::leanh::lean_del_object(v___x_7377_);
                                        crate::leanh::lean_dec(v_snd_7375_);
                                        crate::leanh::lean_dec(v_fst_7374_);
                                        crate::leanh::lean_dec(v_a_7361_);
                                        crate::leanh::lean_dec(v_a_7354_);
                                        crate::leanh::lean_dec_ref(v_e_7325_);
                                        v___x_7603_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(
                                            v_a_7411_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                                        );
                                        crate::leanh::lean_dec_ref_known(v_a_7411_, 3);
                                        v___y_7343_ = v___x_7603_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_7391_);
                                    crate::leanh::lean_dec(v_snd_7389_);
                                    crate::leanh::lean_dec(v_fst_7388_);
                                    crate::leanh::lean_del_object(v___x_7386_);
                                    crate::leanh::lean_del_object(v___x_7377_);
                                    crate::leanh::lean_dec(v_snd_7375_);
                                    crate::leanh::lean_dec(v_fst_7374_);
                                    crate::leanh::lean_dec(v_a_7361_);
                                    crate::leanh::lean_dec(v_a_7354_);
                                    crate::leanh::lean_dec_ref(v_e_7325_);
                                    v___x_7604_ = l_Lean_Meta_coerceMonadLift_x3f___lam__0(
                                        v_a_7411_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                                    );
                                    crate::leanh::lean_dec(v_a_7411_);
                                    v___y_7343_ = v___x_7604_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_7391_);
                                crate::leanh::lean_dec(v_snd_7389_);
                                crate::leanh::lean_dec(v_fst_7388_);
                                crate::leanh::lean_del_object(v___x_7386_);
                                crate::leanh::lean_del_object(v___x_7377_);
                                crate::leanh::lean_dec(v_snd_7375_);
                                crate::leanh::lean_dec(v_fst_7374_);
                                crate::leanh::lean_dec(v_a_7361_);
                                crate::leanh::lean_dec(v_a_7354_);
                                crate::leanh::lean_dec_ref(v_e_7325_);
                                v_a_7605_ = crate::leanh::lean_ctor_get(v___x_7410_, 0);
                                crate::leanh::lean_inc(v_a_7605_);
                                crate::leanh::lean_dec_ref_known(v___x_7410_, 1);
                                v_a_7339_ = v_a_7605_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7391_);
                            crate::leanh::lean_dec(v_snd_7389_);
                            crate::leanh::lean_dec(v_fst_7388_);
                            crate::leanh::lean_del_object(v___x_7386_);
                            crate::leanh::lean_del_object(v___x_7377_);
                            crate::leanh::lean_dec(v_snd_7375_);
                            crate::leanh::lean_dec(v_fst_7374_);
                            crate::leanh::lean_dec(v_a_7361_);
                            crate::leanh::lean_dec(v_a_7354_);
                            crate::leanh::lean_dec_ref(v_e_7325_);
                            v_a_7606_ = crate::leanh::lean_ctor_get(v___x_7408_, 0);
                            crate::leanh::lean_inc(v_a_7606_);
                            crate::leanh::lean_dec_ref_known(v___x_7408_, 1);
                            v_a_7339_ = v_a_7606_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7398_);
                    crate::leanh::lean_del_object(v___x_7391_);
                    crate::leanh::lean_del_object(v___x_7377_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_dec(v_a_7354_);
                    v___x_7607_ = l_Lean_Meta_isMonad_x3f(
                        v_fst_7374_,
                        v_a_7327_,
                        v_a_7328_,
                        v_a_7329_,
                        v_a_7330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7607_) == 0 {
                        v_a_7608_ = crate::leanh::lean_ctor_get(v___x_7607_, 0);
                        v_isSharedCheck_7700_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7607_)) as u8;
                        if v_isSharedCheck_7700_ == 0 {
                            v___x_7610_ = v___x_7607_;
                            v_isShared_7611_ = v_isSharedCheck_7700_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7608_);
                            crate::leanh::lean_dec(v___x_7607_);
                            v___x_7610_ = crate::leanh::lean_box(0);
                            v_isShared_7611_ = v_isSharedCheck_7700_;
                            state = 34;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7394_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_del_object(v___x_7386_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_del_object(v___x_7372_);
                        crate::leanh::lean_del_object(v___x_7363_);
                        crate::leanh::lean_del_object(v___x_7356_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        return v___x_7607_;
                    }
                }
            }
            15 => {
                return v___x_7406_;
            }
            16 => {
                v___x_7433_ = (crate::leanh::lean_unbox(v_a_7429_) as u8);
                crate::leanh::lean_dec(v_a_7429_);
                if v___x_7433_ == 1 {
                    crate::leanh::lean_del_object(v___x_7431_);
                    v___x_7434_ =
                        l_Lean_Meta_decLevel(v_u_7415_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                    if crate::leanh::lean_obj_tag(v___x_7434_) == 0 {
                        v_a_7435_ = crate::leanh::lean_ctor_get(v___x_7434_, 0);
                        crate::leanh::lean_inc(v_a_7435_);
                        crate::leanh::lean_dec_ref_known(v___x_7434_, 1);
                        v___x_7436_ = l_Lean_Meta_decLevel(
                            v_u_7423_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7436_) == 0 {
                            v_a_7437_ = crate::leanh::lean_ctor_get(v___x_7436_, 0);
                            crate::leanh::lean_inc(v_a_7437_);
                            crate::leanh::lean_dec_ref_known(v___x_7436_, 1);
                            v___x_7438_ = l_Lean_Meta_coerceMonadLift_x3f___closed__1;
                            v___x_7439_ = crate::leanh::lean_box(0);
                            if v_isShared_7392_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_7391_, 1);
                                crate::leanh::lean_ctor_set(v___x_7391_, 1, v___x_7439_);
                                crate::leanh::lean_ctor_set(v___x_7391_, 0, v_a_7437_);
                                v___x_7441_ = v___x_7391_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_7586_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7586_, 0, v_a_7437_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7586_, 1, v___x_7439_);
                                v___x_7441_ = v_reuseFailAlloc_7586_;
                                state = 17;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7435_);
                            crate::leanh::lean_dec(v_a_7425_);
                            crate::leanh::lean_del_object(v___x_7391_);
                            crate::leanh::lean_dec(v_snd_7389_);
                            crate::leanh::lean_dec(v_fst_7388_);
                            crate::leanh::lean_del_object(v___x_7386_);
                            crate::leanh::lean_del_object(v___x_7377_);
                            crate::leanh::lean_dec(v_snd_7375_);
                            crate::leanh::lean_dec(v_fst_7374_);
                            crate::leanh::lean_dec(v_a_7361_);
                            crate::leanh::lean_dec(v_a_7354_);
                            crate::leanh::lean_dec_ref(v_e_7325_);
                            v_a_7587_ = crate::leanh::lean_ctor_get(v___x_7436_, 0);
                            crate::leanh::lean_inc(v_a_7587_);
                            crate::leanh::lean_dec_ref_known(v___x_7436_, 1);
                            v_a_7339_ = v_a_7587_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7425_);
                        crate::leanh::lean_dec(v_u_7423_);
                        crate::leanh::lean_del_object(v___x_7391_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_del_object(v___x_7386_);
                        crate::leanh::lean_del_object(v___x_7377_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_dec(v_fst_7374_);
                        crate::leanh::lean_dec(v_a_7361_);
                        crate::leanh::lean_dec(v_a_7354_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        v_a_7588_ = crate::leanh::lean_ctor_get(v___x_7434_, 0);
                        crate::leanh::lean_inc(v_a_7588_);
                        crate::leanh::lean_dec_ref_known(v___x_7434_, 1);
                        v_a_7339_ = v_a_7588_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7425_);
                    crate::leanh::lean_dec(v_u_7423_);
                    crate::leanh::lean_dec(v_u_7415_);
                    crate::leanh::lean_del_object(v___x_7391_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_del_object(v___x_7386_);
                    crate::leanh::lean_del_object(v___x_7377_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v___x_7589_ = crate::leanh::lean_box(0);
                    if v_isShared_7432_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7431_, 0, v___x_7589_);
                        v___x_7591_ = v___x_7431_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_7592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7592_, 0, v___x_7589_);
                        v___x_7591_ = v_reuseFailAlloc_7592_;
                        state = 33;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_7378_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7377_, 1);
                    crate::leanh::lean_ctor_set(v___x_7377_, 1, v___x_7441_);
                    crate::leanh::lean_ctor_set(v___x_7377_, 0, v_a_7435_);
                    v___x_7443_ = v___x_7377_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7585_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 0, v_a_7435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 1, v___x_7441_);
                    v___x_7443_ = v_reuseFailAlloc_7585_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_7444_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7444_, 0, v_a_7425_);
                crate::leanh::lean_ctor_set(v___x_7444_, 1, v___x_7443_);
                v___x_7445_ = l_Lean_Expr_const___override(v___x_7438_, v___x_7444_);
                v___x_7446_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7447_ = lean_mk_empty_array_with_capacity(v___x_7446_);
                crate::leanh::lean_inc(v_fst_7388_);
                v___x_7448_ = lean_array_push(v___x_7447_, v_fst_7388_);
                crate::leanh::lean_inc(v_fst_7374_);
                v___x_7449_ = lean_array_push(v___x_7448_, v_fst_7374_);
                v___x_7450_ = l_Lean_mkAppN(v___x_7445_, v___x_7449_);
                crate::leanh::lean_dec_ref(v___x_7449_);
                v___x_7451_ = crate::leanh::lean_box(0);
                v___x_7452_ = l_Lean_Meta_trySynthInstance(
                    v___x_7450_,
                    v___x_7451_,
                    v_a_7327_,
                    v_a_7328_,
                    v_a_7329_,
                    v_a_7330_,
                );
                if crate::leanh::lean_obj_tag(v___x_7452_) == 0 {
                    v_a_7453_ = crate::leanh::lean_ctor_get(v___x_7452_, 0);
                    v_isSharedCheck_7583_ = (!crate::leanh::lean_is_exclusive(v___x_7452_)) as u8;
                    if v_isSharedCheck_7583_ == 0 {
                        v___x_7455_ = v___x_7452_;
                        v_isShared_7456_ = v_isSharedCheck_7583_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7453_);
                        crate::leanh::lean_dec(v___x_7452_);
                        v___x_7455_ = crate::leanh::lean_box(0);
                        v_isShared_7456_ = v_isSharedCheck_7583_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_del_object(v___x_7386_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v_a_7584_ = crate::leanh::lean_ctor_get(v___x_7452_, 0);
                    crate::leanh::lean_inc(v_a_7584_);
                    crate::leanh::lean_dec_ref_known(v___x_7452_, 1);
                    v_a_7339_ = v_a_7584_;
                    state = 2;
                    continue;
                }
            }
            19 => {
                if crate::leanh::lean_obj_tag(v_a_7453_) == 1 {
                    crate::leanh::lean_del_object(v___x_7455_);
                    v_a_7457_ = crate::leanh::lean_ctor_get(v_a_7453_, 0);
                    crate::leanh::lean_inc(v_a_7457_);
                    crate::leanh::lean_dec_ref_known(v_a_7453_, 1);
                    crate::leanh::lean_inc(v_snd_7389_);
                    v___x_7458_ = l_Lean_Meta_getDecLevel(
                        v_snd_7389_,
                        v_a_7327_,
                        v_a_7328_,
                        v_a_7329_,
                        v_a_7330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7458_) == 0 {
                        v_a_7459_ = crate::leanh::lean_ctor_get(v___x_7458_, 0);
                        crate::leanh::lean_inc(v_a_7459_);
                        crate::leanh::lean_dec_ref_known(v___x_7458_, 1);
                        v___x_7460_ = l_Lean_Meta_getDecLevel(
                            v_a_7361_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7460_) == 0 {
                            v_a_7461_ = crate::leanh::lean_ctor_get(v___x_7460_, 0);
                            crate::leanh::lean_inc(v_a_7461_);
                            crate::leanh::lean_dec_ref_known(v___x_7460_, 1);
                            crate::leanh::lean_inc(v_a_7354_);
                            v___x_7462_ = l_Lean_Meta_getDecLevel(
                                v_a_7354_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7462_) == 0 {
                                v_a_7463_ = crate::leanh::lean_ctor_get(v___x_7462_, 0);
                                crate::leanh::lean_inc(v_a_7463_);
                                crate::leanh::lean_dec_ref_known(v___x_7462_, 1);
                                v___x_7464_ = l_Lean_Meta_coerceMonadLift_x3f___closed__3;
                                v___x_7465_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7465_, 0, v_a_7463_);
                                crate::leanh::lean_ctor_set(v___x_7465_, 1, v___x_7439_);
                                v___x_7466_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7466_, 0, v_a_7461_);
                                crate::leanh::lean_ctor_set(v___x_7466_, 1, v___x_7465_);
                                v___x_7467_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7467_, 0, v_a_7459_);
                                crate::leanh::lean_ctor_set(v___x_7467_, 1, v___x_7466_);
                                crate::leanh::lean_inc_ref(v___x_7467_);
                                v___x_7468_ = l_Lean_mkConst(v___x_7464_, v___x_7467_);
                                v___x_7469_ = crate::leanh::lean_unsigned_to_nat(5);
                                v___x_7470_ = lean_mk_empty_array_with_capacity(v___x_7469_);
                                crate::leanh::lean_inc(v_fst_7388_);
                                v___x_7471_ = lean_array_push(v___x_7470_, v_fst_7388_);
                                crate::leanh::lean_inc(v_fst_7374_);
                                v___x_7472_ = lean_array_push(v___x_7471_, v_fst_7374_);
                                crate::leanh::lean_inc(v_a_7457_);
                                v___x_7473_ = lean_array_push(v___x_7472_, v_a_7457_);
                                crate::leanh::lean_inc(v_snd_7389_);
                                v___x_7474_ = lean_array_push(v___x_7473_, v_snd_7389_);
                                crate::leanh::lean_inc_ref(v_e_7325_);
                                v___x_7475_ = lean_array_push(v___x_7474_, v_e_7325_);
                                v___x_7476_ = l_Lean_mkAppN(v___x_7468_, v___x_7475_);
                                crate::leanh::lean_dec_ref(v___x_7475_);
                                crate::leanh::lean_inc(v_a_7330_);
                                crate::leanh::lean_inc_ref(v_a_7329_);
                                crate::leanh::lean_inc(v_a_7328_);
                                crate::leanh::lean_inc_ref(v_a_7327_);
                                crate::leanh::lean_inc_ref(v___x_7476_);
                                v___x_7477_ = lean_infer_type(
                                    v___x_7476_,
                                    v_a_7327_,
                                    v_a_7328_,
                                    v_a_7329_,
                                    v_a_7330_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_7477_) == 0 {
                                    v_a_7478_ = crate::leanh::lean_ctor_get(v___x_7477_, 0);
                                    crate::leanh::lean_inc(v_a_7478_);
                                    crate::leanh::lean_dec_ref_known(v___x_7477_, 1);
                                    crate::leanh::lean_inc(v_a_7354_);
                                    v___x_7479_ = l_Lean_Meta_isExprDefEq(
                                        v_a_7354_, v_a_7478_, v_a_7327_, v_a_7328_, v_a_7329_,
                                        v_a_7330_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_7479_) == 0 {
                                        v_a_7480_ = crate::leanh::lean_ctor_get(v___x_7479_, 0);
                                        v_isSharedCheck_7574_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_7479_)) as u8;
                                        if v_isSharedCheck_7574_ == 0 {
                                            v___x_7482_ = v___x_7479_;
                                            v_isShared_7483_ = v_isSharedCheck_7574_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_7480_);
                                            crate::leanh::lean_dec(v___x_7479_);
                                            v___x_7482_ = crate::leanh::lean_box(0);
                                            v_isShared_7483_ = v_isSharedCheck_7574_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_7476_);
                                        crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                                        crate::leanh::lean_dec(v_a_7457_);
                                        crate::leanh::lean_dec(v_snd_7389_);
                                        crate::leanh::lean_dec(v_fst_7388_);
                                        crate::leanh::lean_del_object(v___x_7386_);
                                        crate::leanh::lean_dec(v_snd_7375_);
                                        crate::leanh::lean_dec(v_fst_7374_);
                                        crate::leanh::lean_dec(v_a_7354_);
                                        crate::leanh::lean_dec_ref(v_e_7325_);
                                        v_a_7575_ = crate::leanh::lean_ctor_get(v___x_7479_, 0);
                                        crate::leanh::lean_inc(v_a_7575_);
                                        crate::leanh::lean_dec_ref_known(v___x_7479_, 1);
                                        v_a_7339_ = v_a_7575_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_7476_);
                                    crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                                    crate::leanh::lean_dec(v_a_7457_);
                                    crate::leanh::lean_dec(v_snd_7389_);
                                    crate::leanh::lean_dec(v_fst_7388_);
                                    crate::leanh::lean_del_object(v___x_7386_);
                                    crate::leanh::lean_dec(v_snd_7375_);
                                    crate::leanh::lean_dec(v_fst_7374_);
                                    crate::leanh::lean_dec(v_a_7354_);
                                    crate::leanh::lean_dec_ref(v_e_7325_);
                                    v_a_7576_ = crate::leanh::lean_ctor_get(v___x_7477_, 0);
                                    crate::leanh::lean_inc(v_a_7576_);
                                    crate::leanh::lean_dec_ref_known(v___x_7477_, 1);
                                    v_a_7339_ = v_a_7576_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7461_);
                                crate::leanh::lean_dec(v_a_7459_);
                                crate::leanh::lean_dec(v_a_7457_);
                                crate::leanh::lean_dec(v_snd_7389_);
                                crate::leanh::lean_dec(v_fst_7388_);
                                crate::leanh::lean_del_object(v___x_7386_);
                                crate::leanh::lean_dec(v_snd_7375_);
                                crate::leanh::lean_dec(v_fst_7374_);
                                crate::leanh::lean_dec(v_a_7354_);
                                crate::leanh::lean_dec_ref(v_e_7325_);
                                v_a_7577_ = crate::leanh::lean_ctor_get(v___x_7462_, 0);
                                crate::leanh::lean_inc(v_a_7577_);
                                crate::leanh::lean_dec_ref_known(v___x_7462_, 1);
                                v_a_7339_ = v_a_7577_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7459_);
                            crate::leanh::lean_dec(v_a_7457_);
                            crate::leanh::lean_dec(v_snd_7389_);
                            crate::leanh::lean_dec(v_fst_7388_);
                            crate::leanh::lean_del_object(v___x_7386_);
                            crate::leanh::lean_dec(v_snd_7375_);
                            crate::leanh::lean_dec(v_fst_7374_);
                            crate::leanh::lean_dec(v_a_7354_);
                            crate::leanh::lean_dec_ref(v_e_7325_);
                            v_a_7578_ = crate::leanh::lean_ctor_get(v___x_7460_, 0);
                            crate::leanh::lean_inc(v_a_7578_);
                            crate::leanh::lean_dec_ref_known(v___x_7460_, 1);
                            v_a_7339_ = v_a_7578_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7457_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_del_object(v___x_7386_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_dec(v_fst_7374_);
                        crate::leanh::lean_dec(v_a_7361_);
                        crate::leanh::lean_dec(v_a_7354_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        v_a_7579_ = crate::leanh::lean_ctor_get(v___x_7458_, 0);
                        crate::leanh::lean_inc(v_a_7579_);
                        crate::leanh::lean_dec_ref_known(v___x_7458_, 1);
                        v_a_7339_ = v_a_7579_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7453_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_del_object(v___x_7386_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7361_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    if v_isShared_7456_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7455_, 0, v___x_7451_);
                        v___x_7581_ = v___x_7455_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_7582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7582_, 0, v___x_7451_);
                        v___x_7581_ = v_reuseFailAlloc_7582_;
                        state = 32;
                        continue;
                    }
                }
            }
            20 => {
                v___x_7484_ = (crate::leanh::lean_unbox(v_a_7480_) as u8);
                crate::leanh::lean_dec(v_a_7480_);
                if v___x_7484_ == 0 {
                    crate::leanh::lean_del_object(v___x_7482_);
                    crate::leanh::lean_dec_ref(v___x_7476_);
                    crate::leanh::lean_del_object(v___x_7386_);
                    crate::leanh::lean_inc(v_fst_7374_);
                    v___x_7485_ = l_Lean_Meta_isMonad_x3f(
                        v_fst_7374_,
                        v_a_7327_,
                        v_a_7328_,
                        v_a_7329_,
                        v_a_7330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7485_) == 0 {
                        v_a_7486_ = crate::leanh::lean_ctor_get(v___x_7485_, 0);
                        v_isSharedCheck_7566_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7485_)) as u8;
                        if v_isSharedCheck_7566_ == 0 {
                            v___x_7488_ = v___x_7485_;
                            v_isShared_7489_ = v_isSharedCheck_7566_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7486_);
                            crate::leanh::lean_dec(v___x_7485_);
                            v___x_7488_ = crate::leanh::lean_box(0);
                            v_isShared_7489_ = v_isSharedCheck_7566_;
                            state = 21;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                        crate::leanh::lean_dec(v_a_7457_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_dec(v_fst_7374_);
                        crate::leanh::lean_dec(v_a_7354_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        v_a_7567_ = crate::leanh::lean_ctor_get(v___x_7485_, 0);
                        crate::leanh::lean_inc(v_a_7567_);
                        crate::leanh::lean_dec_ref_known(v___x_7485_, 1);
                        v_a_7339_ = v_a_7567_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                    crate::leanh::lean_dec(v_a_7457_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    if v_isShared_7387_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7386_, 0, v___x_7476_);
                        v___x_7569_ = v___x_7386_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_7573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7573_, 0, v___x_7476_);
                        v___x_7569_ = v_reuseFailAlloc_7573_;
                        state = 30;
                        continue;
                    }
                }
            }
            21 => {
                if crate::leanh::lean_obj_tag(v_a_7486_) == 1 {
                    crate::leanh::lean_del_object(v___x_7488_);
                    v_val_7490_ = crate::leanh::lean_ctor_get(v_a_7486_, 0);
                    v_isSharedCheck_7562_ = (!crate::leanh::lean_is_exclusive(v_a_7486_)) as u8;
                    if v_isSharedCheck_7562_ == 0 {
                        v___x_7492_ = v_a_7486_;
                        v_isShared_7493_ = v_isSharedCheck_7562_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7490_);
                        crate::leanh::lean_dec(v_a_7486_);
                        v___x_7492_ = crate::leanh::lean_box(0);
                        v_isShared_7493_ = v_isSharedCheck_7562_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7486_);
                    crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                    crate::leanh::lean_dec(v_a_7457_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    if v_isShared_7489_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7488_, 0, v___x_7451_);
                        v___x_7564_ = v___x_7488_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_7565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7565_, 0, v___x_7451_);
                        v___x_7564_ = v_reuseFailAlloc_7565_;
                        state = 29;
                        continue;
                    }
                }
            }
            22 => {
                crate::leanh::lean_inc(v_snd_7389_);
                v___x_7494_ =
                    l_Lean_Meta_getLevel(v_snd_7389_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                if crate::leanh::lean_obj_tag(v___x_7494_) == 0 {
                    v_a_7495_ = crate::leanh::lean_ctor_get(v___x_7494_, 0);
                    crate::leanh::lean_inc(v_a_7495_);
                    crate::leanh::lean_dec_ref_known(v___x_7494_, 1);
                    crate::leanh::lean_inc(v_snd_7375_);
                    v___x_7496_ = l_Lean_Meta_getLevel(
                        v_snd_7375_,
                        v_a_7327_,
                        v_a_7328_,
                        v_a_7329_,
                        v_a_7330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7496_) == 0 {
                        v_a_7497_ = crate::leanh::lean_ctor_get(v___x_7496_, 0);
                        crate::leanh::lean_inc(v_a_7497_);
                        crate::leanh::lean_dec_ref_known(v___x_7496_, 1);
                        v___x_7498_ = l_Lean_Meta_coerceMonadLift_x3f___closed__5;
                        v___x_7499_ = 0;
                        v___x_7500_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f___closed__1;
                        v___x_7501_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7501_, 0, v_a_7497_);
                        crate::leanh::lean_ctor_set(v___x_7501_, 1, v___x_7439_);
                        v___x_7502_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7502_, 0, v_a_7495_);
                        crate::leanh::lean_ctor_set(v___x_7502_, 1, v___x_7501_);
                        v___x_7503_ = l_Lean_mkConst(v___x_7500_, v___x_7502_);
                        v___x_7504_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_coerceMonadLift_x3f___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_coerceMonadLift_x3f___closed__6_once
                            ),
                            _init_l_Lean_Meta_coerceMonadLift_x3f___closed__6,
                        );
                        v___x_7505_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_7506_ = lean_mk_empty_array_with_capacity(v___x_7505_);
                        crate::leanh::lean_inc_n(v_snd_7389_, 2);
                        v___x_7507_ = lean_array_push(v___x_7506_, v_snd_7389_);
                        v___x_7508_ = lean_array_push(v___x_7507_, v___x_7504_);
                        crate::leanh::lean_inc(v_snd_7375_);
                        v___x_7509_ = lean_array_push(v___x_7508_, v_snd_7375_);
                        v___x_7510_ = l_Lean_mkAppN(v___x_7503_, v___x_7509_);
                        crate::leanh::lean_dec_ref(v___x_7509_);
                        v___x_7511_ =
                            l_Lean_mkForall(v___x_7498_, v___x_7499_, v_snd_7389_, v___x_7510_);
                        v___x_7512_ = l_Lean_Meta_trySynthInstance(
                            v___x_7511_,
                            v___x_7451_,
                            v_a_7327_,
                            v_a_7328_,
                            v_a_7329_,
                            v_a_7330_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7512_) == 0 {
                            v_a_7513_ = crate::leanh::lean_ctor_get(v___x_7512_, 0);
                            v_isSharedCheck_7558_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7512_)) as u8;
                            if v_isSharedCheck_7558_ == 0 {
                                v___x_7515_ = v___x_7512_;
                                v_isShared_7516_ = v_isSharedCheck_7558_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7513_);
                                crate::leanh::lean_dec(v___x_7512_);
                                v___x_7515_ = crate::leanh::lean_box(0);
                                v_isShared_7516_ = v_isSharedCheck_7558_;
                                state = 23;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7492_);
                            crate::leanh::lean_dec(v_val_7490_);
                            crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                            crate::leanh::lean_dec(v_a_7457_);
                            crate::leanh::lean_dec(v_snd_7389_);
                            crate::leanh::lean_dec(v_fst_7388_);
                            crate::leanh::lean_dec(v_snd_7375_);
                            crate::leanh::lean_dec(v_fst_7374_);
                            crate::leanh::lean_dec(v_a_7354_);
                            crate::leanh::lean_dec_ref(v_e_7325_);
                            v_a_7559_ = crate::leanh::lean_ctor_get(v___x_7512_, 0);
                            crate::leanh::lean_inc(v_a_7559_);
                            crate::leanh::lean_dec_ref_known(v___x_7512_, 1);
                            v_a_7339_ = v_a_7559_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7495_);
                        crate::leanh::lean_del_object(v___x_7492_);
                        crate::leanh::lean_dec(v_val_7490_);
                        crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                        crate::leanh::lean_dec(v_a_7457_);
                        crate::leanh::lean_dec(v_snd_7389_);
                        crate::leanh::lean_dec(v_fst_7388_);
                        crate::leanh::lean_dec(v_snd_7375_);
                        crate::leanh::lean_dec(v_fst_7374_);
                        crate::leanh::lean_dec(v_a_7354_);
                        crate::leanh::lean_dec_ref(v_e_7325_);
                        v_a_7560_ = crate::leanh::lean_ctor_get(v___x_7496_, 0);
                        crate::leanh::lean_inc(v_a_7560_);
                        crate::leanh::lean_dec_ref_known(v___x_7496_, 1);
                        v_a_7339_ = v_a_7560_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7492_);
                    crate::leanh::lean_dec(v_val_7490_);
                    crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                    crate::leanh::lean_dec(v_a_7457_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v_a_7561_ = crate::leanh::lean_ctor_get(v___x_7494_, 0);
                    crate::leanh::lean_inc(v_a_7561_);
                    crate::leanh::lean_dec_ref_known(v___x_7494_, 1);
                    v_a_7339_ = v_a_7561_;
                    state = 2;
                    continue;
                }
            }
            23 => {
                if crate::leanh::lean_obj_tag(v_a_7513_) == 1 {
                    crate::leanh::lean_del_object(v___x_7515_);
                    v_a_7517_ = crate::leanh::lean_ctor_get(v_a_7513_, 0);
                    crate::leanh::lean_inc(v_a_7517_);
                    crate::leanh::lean_dec_ref_known(v_a_7513_, 1);
                    v___x_7518_ = l_Lean_Meta_coerceMonadLift_x3f___closed__9;
                    v___x_7519_ = l_Lean_mkConst(v___x_7518_, v___x_7467_);
                    v___x_7520_ = crate::leanh::lean_unsigned_to_nat(8);
                    v___x_7521_ = lean_mk_empty_array_with_capacity(v___x_7520_);
                    v___x_7522_ = lean_array_push(v___x_7521_, v_fst_7388_);
                    v___x_7523_ = lean_array_push(v___x_7522_, v_fst_7374_);
                    v___x_7524_ = lean_array_push(v___x_7523_, v_snd_7389_);
                    v___x_7525_ = lean_array_push(v___x_7524_, v_snd_7375_);
                    v___x_7526_ = lean_array_push(v___x_7525_, v_a_7457_);
                    v___x_7527_ = lean_array_push(v___x_7526_, v_a_7517_);
                    v___x_7528_ = lean_array_push(v___x_7527_, v_val_7490_);
                    v___x_7529_ = lean_array_push(v___x_7528_, v_e_7325_);
                    v___x_7530_ = l_Lean_mkAppN(v___x_7519_, v___x_7529_);
                    crate::leanh::lean_dec_ref(v___x_7529_);
                    v___x_7531_ = l_Lean_Meta_expandCoe(
                        v___x_7530_,
                        v_a_7327_,
                        v_a_7328_,
                        v_a_7329_,
                        v_a_7330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7531_) == 0 {
                        v_a_7532_ = crate::leanh::lean_ctor_get(v___x_7531_, 0);
                        crate::leanh::lean_inc(v_a_7532_);
                        crate::leanh::lean_dec_ref_known(v___x_7531_, 1);
                        v_fst_7533_ = crate::leanh::lean_ctor_get(v_a_7532_, 0);
                        crate::leanh::lean_inc_n(v_fst_7533_, 2);
                        crate::leanh::lean_dec(v_a_7532_);
                        crate::leanh::lean_inc(v_a_7330_);
                        crate::leanh::lean_inc_ref(v_a_7329_);
                        crate::leanh::lean_inc(v_a_7328_);
                        crate::leanh::lean_inc_ref(v_a_7327_);
                        v___x_7534_ = lean_infer_type(
                            v_fst_7533_,
                            v_a_7327_,
                            v_a_7328_,
                            v_a_7329_,
                            v_a_7330_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7534_) == 0 {
                            v_a_7535_ = crate::leanh::lean_ctor_get(v___x_7534_, 0);
                            crate::leanh::lean_inc(v_a_7535_);
                            crate::leanh::lean_dec_ref_known(v___x_7534_, 1);
                            v___x_7536_ = l_Lean_Meta_isExprDefEq(
                                v_a_7354_, v_a_7535_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7536_) == 0 {
                                v_a_7537_ = crate::leanh::lean_ctor_get(v___x_7536_, 0);
                                v_isSharedCheck_7551_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7536_)) as u8;
                                if v_isSharedCheck_7551_ == 0 {
                                    v___x_7539_ = v___x_7536_;
                                    v_isShared_7540_ = v_isSharedCheck_7551_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7537_);
                                    crate::leanh::lean_dec(v___x_7536_);
                                    v___x_7539_ = crate::leanh::lean_box(0);
                                    v_isShared_7540_ = v_isSharedCheck_7551_;
                                    state = 24;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_7533_);
                                crate::leanh::lean_del_object(v___x_7492_);
                                v_a_7552_ = crate::leanh::lean_ctor_get(v___x_7536_, 0);
                                crate::leanh::lean_inc(v_a_7552_);
                                crate::leanh::lean_dec_ref_known(v___x_7536_, 1);
                                v_a_7339_ = v_a_7552_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_7533_);
                            crate::leanh::lean_del_object(v___x_7492_);
                            crate::leanh::lean_dec(v_a_7354_);
                            v_a_7553_ = crate::leanh::lean_ctor_get(v___x_7534_, 0);
                            crate::leanh::lean_inc(v_a_7553_);
                            crate::leanh::lean_dec_ref_known(v___x_7534_, 1);
                            v_a_7339_ = v_a_7553_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_7492_);
                        crate::leanh::lean_dec(v_a_7354_);
                        v_a_7554_ = crate::leanh::lean_ctor_get(v___x_7531_, 0);
                        crate::leanh::lean_inc(v_a_7554_);
                        crate::leanh::lean_dec_ref_known(v___x_7531_, 1);
                        v_a_7339_ = v_a_7554_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7513_);
                    crate::leanh::lean_del_object(v___x_7492_);
                    crate::leanh::lean_dec(v_val_7490_);
                    crate::leanh::lean_dec_ref_known(v___x_7467_, 2);
                    crate::leanh::lean_dec(v_a_7457_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_dec(v_fst_7374_);
                    crate::leanh::lean_dec(v_a_7354_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    if v_isShared_7516_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7515_, 0, v___x_7451_);
                        v___x_7556_ = v___x_7515_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_7557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7557_, 0, v___x_7451_);
                        v___x_7556_ = v_reuseFailAlloc_7557_;
                        state = 28;
                        continue;
                    }
                }
            }
            24 => {
                v___x_7541_ = (crate::leanh::lean_unbox(v_a_7537_) as u8);
                crate::leanh::lean_dec(v_a_7537_);
                if v___x_7541_ == 0 {
                    crate::leanh::lean_dec(v_fst_7533_);
                    crate::leanh::lean_del_object(v___x_7492_);
                    if v_isShared_7540_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7539_, 0, v___x_7451_);
                        v___x_7543_ = v___x_7539_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_7544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7544_, 0, v___x_7451_);
                        v___x_7543_ = v_reuseFailAlloc_7544_;
                        state = 25;
                        continue;
                    }
                } else {
                    if v_isShared_7493_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7492_, 0, v_fst_7533_);
                        v___x_7546_ = v___x_7492_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_7550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 0, v_fst_7533_);
                        v___x_7546_ = v_reuseFailAlloc_7550_;
                        state = 26;
                        continue;
                    }
                }
            }
            25 => {
                return v___x_7543_;
            }
            26 => {
                if v_isShared_7540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7539_, 0, v___x_7546_);
                    v___x_7548_ = v___x_7539_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7549_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 0, v___x_7546_);
                    v___x_7548_ = v_reuseFailAlloc_7549_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_7548_;
            }
            28 => {
                return v___x_7556_;
            }
            29 => {
                return v___x_7564_;
            }
            30 => {
                if v_isShared_7483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7482_, 0, v___x_7569_);
                    v___x_7571_ = v___x_7482_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7572_, 0, v___x_7569_);
                    v___x_7571_ = v_reuseFailAlloc_7572_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7571_;
            }
            32 => {
                return v___x_7581_;
            }
            33 => {
                return v___x_7591_;
            }
            34 => {
                if crate::leanh::lean_obj_tag(v_a_7608_) == 1 {
                    v___x_7612_ = l_Lean_Meta_coerceMonadLift_x3f___closed__11;
                    if v_isShared_7387_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7386_, 0, v_fst_7388_);
                        v___x_7614_ = v___x_7386_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_7681_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 0, v_fst_7388_);
                        v___x_7614_ = v_reuseFailAlloc_7681_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7610_);
                    crate::leanh::lean_dec(v_a_7608_);
                    crate::leanh::lean_dec(v_snd_7389_);
                    crate::leanh::lean_dec(v_fst_7388_);
                    crate::leanh::lean_del_object(v___x_7386_);
                    crate::leanh::lean_dec(v_snd_7375_);
                    crate::leanh::lean_del_object(v___x_7372_);
                    crate::leanh::lean_del_object(v___x_7363_);
                    crate::leanh::lean_del_object(v___x_7356_);
                    crate::leanh::lean_dec_ref(v_e_7325_);
                    v___x_7682_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_7394_, v_a_7328_, v_a_7330_);
                    crate::leanh::lean_dec(v_a_7394_);
                    if crate::leanh::lean_obj_tag(v___x_7682_) == 0 {
                        v_isSharedCheck_7690_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7682_)) as u8;
                        if v_isSharedCheck_7690_ == 0 {
                            v_unused_7691_ = crate::leanh::lean_ctor_get(v___x_7682_, 0);
                            crate::leanh::lean_dec(v_unused_7691_);
                            v___x_7684_ = v___x_7682_;
                            v_isShared_7685_ = v_isSharedCheck_7690_;
                            state = 50;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7682_);
                            v___x_7684_ = crate::leanh::lean_box(0);
                            v_isShared_7685_ = v_isSharedCheck_7690_;
                            state = 50;
                            continue;
                        }
                    } else {
                        v_a_7692_ = crate::leanh::lean_ctor_get(v___x_7682_, 0);
                        v_isSharedCheck_7699_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7682_)) as u8;
                        if v_isSharedCheck_7699_ == 0 {
                            v___x_7694_ = v___x_7682_;
                            v_isShared_7695_ = v_isSharedCheck_7699_;
                            state = 52;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7692_);
                            crate::leanh::lean_dec(v___x_7682_);
                            v___x_7694_ = crate::leanh::lean_box(0);
                            v_isShared_7695_ = v_isSharedCheck_7699_;
                            state = 52;
                            continue;
                        }
                    }
                }
            }
            35 => {
                if v_isShared_7373_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7372_, 0, v_snd_7389_);
                    v___x_7616_ = v___x_7372_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_7680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7680_, 0, v_snd_7389_);
                    v___x_7616_ = v_reuseFailAlloc_7680_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_7364_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7363_, 1);
                    crate::leanh::lean_ctor_set(v___x_7363_, 0, v_snd_7375_);
                    v___x_7618_ = v___x_7363_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_7679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7679_, 0, v_snd_7375_);
                    v___x_7618_ = v_reuseFailAlloc_7679_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_7619_ = crate::leanh::lean_box(0);
                if v_isShared_7357_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7356_, 1);
                    crate::leanh::lean_ctor_set(v___x_7356_, 0, v_e_7325_);
                    v___x_7648_ = v___x_7356_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_7678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7678_, 0, v_e_7325_);
                    v___x_7648_ = v_reuseFailAlloc_7678_;
                    state = 45;
                    continue;
                }
            }
            38 => {
                if v___y_7622_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_7621_);
                    crate::leanh::lean_del_object(v___x_7610_);
                    v___x_7623_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_7394_, v_a_7328_, v_a_7330_);
                    crate::leanh::lean_dec(v_a_7394_);
                    if crate::leanh::lean_obj_tag(v___x_7623_) == 0 {
                        v_isSharedCheck_7630_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7623_)) as u8;
                        if v_isSharedCheck_7630_ == 0 {
                            v_unused_7631_ = crate::leanh::lean_ctor_get(v___x_7623_, 0);
                            crate::leanh::lean_dec(v_unused_7631_);
                            v___x_7625_ = v___x_7623_;
                            v_isShared_7626_ = v_isSharedCheck_7630_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7623_);
                            v___x_7625_ = crate::leanh::lean_box(0);
                            v_isShared_7626_ = v_isSharedCheck_7630_;
                            state = 39;
                            continue;
                        }
                    } else {
                        v_a_7632_ = crate::leanh::lean_ctor_get(v___x_7623_, 0);
                        v_isSharedCheck_7639_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7623_)) as u8;
                        if v_isSharedCheck_7639_ == 0 {
                            v___x_7634_ = v___x_7623_;
                            v_isShared_7635_ = v_isSharedCheck_7639_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7632_);
                            crate::leanh::lean_dec(v___x_7623_);
                            v___x_7634_ = crate::leanh::lean_box(0);
                            v_isShared_7635_ = v_isSharedCheck_7639_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7394_);
                    if v_isShared_7611_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7610_, 1);
                        crate::leanh::lean_ctor_set(v___x_7610_, 0, v___y_7621_);
                        v___x_7641_ = v___x_7610_;
                        state = 43;
                        continue;
                    } else {
                        v_reuseFailAlloc_7642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7642_, 0, v___y_7621_);
                        v___x_7641_ = v_reuseFailAlloc_7642_;
                        state = 43;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_7626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7625_, 0, v___x_7619_);
                    v___x_7628_ = v___x_7625_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_7629_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7629_, 0, v___x_7619_);
                    v___x_7628_ = v_reuseFailAlloc_7629_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_7628_;
            }
            41 => {
                if v_isShared_7635_ == 0 {
                    v___x_7637_ = v___x_7634_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_7638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7638_, 0, v_a_7632_);
                    v___x_7637_ = v_reuseFailAlloc_7638_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_7637_;
            }
            43 => {
                return v___x_7641_;
            }
            44 => {
                v___x_7645_ = l_Lean_Exception_isInterrupt(v_a_7644_);
                if v___x_7645_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_7644_);
                    v___x_7646_ = l_Lean_Exception_isRuntime(v_a_7644_);
                    v___y_7621_ = v_a_7644_;
                    v___y_7622_ = v___x_7646_;
                    state = 38;
                    continue;
                } else {
                    v___y_7621_ = v_a_7644_;
                    v___y_7622_ = v___x_7645_;
                    state = 38;
                    continue;
                }
            }
            45 => {
                v___x_7649_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_7650_ = lean_mk_empty_array_with_capacity(v___x_7649_);
                v___x_7651_ = lean_array_push(v___x_7650_, v___x_7614_);
                v___x_7652_ = lean_array_push(v___x_7651_, v___x_7616_);
                v___x_7653_ = lean_array_push(v___x_7652_, v___x_7618_);
                v___x_7654_ = lean_array_push(v___x_7653_, v___x_7619_);
                v___x_7655_ = lean_array_push(v___x_7654_, v_a_7608_);
                v___x_7656_ = lean_array_push(v___x_7655_, v___x_7648_);
                v___x_7657_ = l_Lean_Meta_mkAppOptM(
                    v___x_7612_,
                    v___x_7656_,
                    v_a_7327_,
                    v_a_7328_,
                    v_a_7329_,
                    v_a_7330_,
                );
                if crate::leanh::lean_obj_tag(v___x_7657_) == 0 {
                    v_a_7658_ = crate::leanh::lean_ctor_get(v___x_7657_, 0);
                    v_isSharedCheck_7676_ = (!crate::leanh::lean_is_exclusive(v___x_7657_)) as u8;
                    if v_isSharedCheck_7676_ == 0 {
                        v___x_7660_ = v___x_7657_;
                        v_isShared_7661_ = v_isSharedCheck_7676_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7658_);
                        crate::leanh::lean_dec(v___x_7657_);
                        v___x_7660_ = crate::leanh::lean_box(0);
                        v_isShared_7661_ = v_isSharedCheck_7676_;
                        state = 46;
                        continue;
                    }
                } else {
                    v_a_7677_ = crate::leanh::lean_ctor_get(v___x_7657_, 0);
                    crate::leanh::lean_inc(v_a_7677_);
                    crate::leanh::lean_dec_ref_known(v___x_7657_, 1);
                    v_a_7644_ = v_a_7677_;
                    state = 44;
                    continue;
                }
            }
            46 => {
                v___x_7662_ =
                    l_Lean_Meta_expandCoe(v_a_7658_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_);
                if crate::leanh::lean_obj_tag(v___x_7662_) == 0 {
                    crate::leanh::lean_del_object(v___x_7610_);
                    crate::leanh::lean_dec(v_a_7394_);
                    v_a_7663_ = crate::leanh::lean_ctor_get(v___x_7662_, 0);
                    v_isSharedCheck_7674_ = (!crate::leanh::lean_is_exclusive(v___x_7662_)) as u8;
                    if v_isSharedCheck_7674_ == 0 {
                        v___x_7665_ = v___x_7662_;
                        v_isShared_7666_ = v_isSharedCheck_7674_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7663_);
                        crate::leanh::lean_dec(v___x_7662_);
                        v___x_7665_ = crate::leanh::lean_box(0);
                        v_isShared_7666_ = v_isSharedCheck_7674_;
                        state = 47;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7660_);
                    v_a_7675_ = crate::leanh::lean_ctor_get(v___x_7662_, 0);
                    crate::leanh::lean_inc(v_a_7675_);
                    crate::leanh::lean_dec_ref_known(v___x_7662_, 1);
                    v_a_7644_ = v_a_7675_;
                    state = 44;
                    continue;
                }
            }
            47 => {
                v_fst_7667_ = crate::leanh::lean_ctor_get(v_a_7663_, 0);
                crate::leanh::lean_inc(v_fst_7667_);
                crate::leanh::lean_dec(v_a_7663_);
                if v_isShared_7661_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7660_, 1);
                    crate::leanh::lean_ctor_set(v___x_7660_, 0, v_fst_7667_);
                    v___x_7669_ = v___x_7660_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7673_, 0, v_fst_7667_);
                    v___x_7669_ = v_reuseFailAlloc_7673_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                if v_isShared_7666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7665_, 0, v___x_7669_);
                    v___x_7671_ = v___x_7665_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_7672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7672_, 0, v___x_7669_);
                    v___x_7671_ = v_reuseFailAlloc_7672_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_7671_;
            }
            50 => {
                v___x_7686_ = crate::leanh::lean_box(0);
                if v_isShared_7685_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7684_, 0, v___x_7686_);
                    v___x_7688_ = v___x_7684_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_7689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7689_, 0, v___x_7686_);
                    v___x_7688_ = v_reuseFailAlloc_7689_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_7688_;
            }
            52 => {
                if v_isShared_7695_ == 0 {
                    v___x_7697_ = v___x_7694_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_7698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7698_, 0, v_a_7692_);
                    v___x_7697_ = v_reuseFailAlloc_7698_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_7697_;
            }
            54 => {
                if v_isShared_7705_ == 0 {
                    v___x_7707_ = v___x_7704_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_7708_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7708_, 0, v_a_7702_);
                    v___x_7707_ = v_reuseFailAlloc_7708_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_7707_;
            }
            56 => {
                if v_isShared_7713_ == 0 {
                    v___x_7715_ = v___x_7712_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_7716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 0, v_a_7710_);
                    v___x_7715_ = v_reuseFailAlloc_7716_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_7715_;
            }
            58 => {
                return v___x_7722_;
            }
            59 => {
                if v_isShared_7728_ == 0 {
                    v___x_7730_ = v___x_7727_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_7731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v_a_7725_);
                    v___x_7730_ = v_reuseFailAlloc_7731_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_7730_;
            }
            61 => {
                return v___x_7737_;
            }
            62 => {
                if v_isShared_7743_ == 0 {
                    v___x_7745_ = v___x_7742_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_7746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7746_, 0, v_a_7740_);
                    v___x_7745_ = v_reuseFailAlloc_7746_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_7745_;
            }
            64 => {
                if v_isShared_7752_ == 0 {
                    v___x_7754_ = v___x_7751_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_7755_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 0, v_a_7749_);
                    v___x_7754_ = v_reuseFailAlloc_7755_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_7754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerceMonadLift_x3f___boxed(
    mut v_e_7758_: *mut crate::leanh::LeanObject,
    mut v_expectedType_7759_: *mut crate::leanh::LeanObject,
    mut v_a_7760_: *mut crate::leanh::LeanObject,
    mut v_a_7761_: *mut crate::leanh::LeanObject,
    mut v_a_7762_: *mut crate::leanh::LeanObject,
    mut v_a_7763_: *mut crate::leanh::LeanObject,
    mut v_a_7764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7765_ = l_Lean_Meta_coerceMonadLift_x3f(
        v_e_7758_,
        v_expectedType_7759_,
        v_a_7760_,
        v_a_7761_,
        v_a_7762_,
        v_a_7763_,
    );
    crate::leanh::lean_dec(v_a_7763_);
    crate::leanh::lean_dec_ref(v_a_7762_);
    crate::leanh::lean_dec(v_a_7761_);
    crate::leanh::lean_dec_ref(v_a_7760_);
    return v_res_7765_;
}
pub unsafe fn l_Lean_Meta_coerceCollectingNames_x3f(
    mut v_expr_7766_: *mut crate::leanh::LeanObject,
    mut v_expectedType_7767_: *mut crate::leanh::LeanObject,
    mut v_a_7768_: *mut crate::leanh::LeanObject,
    mut v_a_7769_: *mut crate::leanh::LeanObject,
    mut v_a_7770_: *mut crate::leanh::LeanObject,
    mut v_a_7771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7777_: u8 = 0;
    let mut v_val_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7781_: u8 = 0;
    let mut v___x_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7790_: u8 = 0;
    let mut v___x_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: u8 = 0;
    let mut v___x_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7800_: u8 = 0;
    let mut v___x_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7807_: u8 = 0;
    let mut v___x_7808_: u8 = 0;
    let mut v___x_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7818_: u8 = 0;
    let mut v_a_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7822_: u8 = 0;
    let mut v___x_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7826_: u8 = 0;
    let mut v_a_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7830_: u8 = 0;
    let mut v___x_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7834_: u8 = 0;
    let mut v_isSharedCheck_7835_: u8 = 0;
    let mut v___x_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7840_: u8 = 0;
    let mut v___x_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7844_: u8 = 0;
    let mut v_a_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7848_: u8 = 0;
    let mut v___x_7850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7852_: u8 = 0;
    let mut v_isSharedCheck_7853_: u8 = 0;
    let mut v_a_7854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7857_: u8 = 0;
    let mut v___x_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_expectedType_7767_);
                crate::leanh::lean_inc_ref(v_expr_7766_);
                v___x_7773_ = l_Lean_Meta_coerceMonadLift_x3f(
                    v_expr_7766_,
                    v_expectedType_7767_,
                    v_a_7768_,
                    v_a_7769_,
                    v_a_7770_,
                    v_a_7771_,
                );
                if crate::leanh::lean_obj_tag(v___x_7773_) == 0 {
                    v_a_7774_ = crate::leanh::lean_ctor_get(v___x_7773_, 0);
                    v_isSharedCheck_7853_ = (!crate::leanh::lean_is_exclusive(v___x_7773_)) as u8;
                    if v_isSharedCheck_7853_ == 0 {
                        v___x_7776_ = v___x_7773_;
                        v_isShared_7777_ = v_isSharedCheck_7853_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7774_);
                        crate::leanh::lean_dec(v___x_7773_);
                        v___x_7776_ = crate::leanh::lean_box(0);
                        v_isShared_7777_ = v_isSharedCheck_7853_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_expectedType_7767_);
                    crate::leanh::lean_dec_ref(v_expr_7766_);
                    v_a_7854_ = crate::leanh::lean_ctor_get(v___x_7773_, 0);
                    v_isSharedCheck_7861_ = (!crate::leanh::lean_is_exclusive(v___x_7773_)) as u8;
                    if v_isSharedCheck_7861_ == 0 {
                        v___x_7856_ = v___x_7773_;
                        v_isShared_7857_ = v_isSharedCheck_7861_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7854_);
                        crate::leanh::lean_dec(v___x_7773_);
                        v___x_7856_ = crate::leanh::lean_box(0);
                        v_isShared_7857_ = v_isSharedCheck_7861_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7774_) == 1 {
                    crate::leanh::lean_dec_ref(v_expectedType_7767_);
                    crate::leanh::lean_dec_ref(v_expr_7766_);
                    v_val_7778_ = crate::leanh::lean_ctor_get(v_a_7774_, 0);
                    v_isSharedCheck_7790_ = (!crate::leanh::lean_is_exclusive(v_a_7774_)) as u8;
                    if v_isSharedCheck_7790_ == 0 {
                        v___x_7780_ = v_a_7774_;
                        v_isShared_7781_ = v_isSharedCheck_7790_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7778_);
                        crate::leanh::lean_dec(v_a_7774_);
                        v___x_7780_ = crate::leanh::lean_box(0);
                        v_isShared_7781_ = v_isSharedCheck_7790_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7776_);
                    crate::leanh::lean_dec(v_a_7774_);
                    crate::leanh::lean_inc_ref(v_expectedType_7767_);
                    v___x_7791_ = l_Lean_Meta_whnfR(
                        v_expectedType_7767_,
                        v_a_7768_,
                        v_a_7769_,
                        v_a_7770_,
                        v_a_7771_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7791_) == 0 {
                        v_a_7792_ = crate::leanh::lean_ctor_get(v___x_7791_, 0);
                        crate::leanh::lean_inc(v_a_7792_);
                        crate::leanh::lean_dec_ref_known(v___x_7791_, 1);
                        v___x_7793_ = l_Lean_Expr_isForall(v_a_7792_);
                        crate::leanh::lean_dec(v_a_7792_);
                        if v___x_7793_ == 0 {
                            v___x_7794_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(
                                v_expr_7766_,
                                v_expectedType_7767_,
                                v_a_7768_,
                                v_a_7769_,
                                v_a_7770_,
                                v_a_7771_,
                            );
                            return v___x_7794_;
                        } else {
                            crate::leanh::lean_inc_ref(v_expr_7766_);
                            v___x_7795_ = l_Lean_Meta_coerceToFunction_x3f(
                                v_expr_7766_,
                                v_a_7768_,
                                v_a_7769_,
                                v_a_7770_,
                                v_a_7771_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7795_) == 0 {
                                v_a_7796_ = crate::leanh::lean_ctor_get(v___x_7795_, 0);
                                crate::leanh::lean_inc(v_a_7796_);
                                crate::leanh::lean_dec_ref_known(v___x_7795_, 1);
                                if crate::leanh::lean_obj_tag(v_a_7796_) == 1 {
                                    v_val_7797_ = crate::leanh::lean_ctor_get(v_a_7796_, 0);
                                    v_isSharedCheck_7835_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_7796_)) as u8;
                                    if v_isSharedCheck_7835_ == 0 {
                                        v___x_7799_ = v_a_7796_;
                                        v_isShared_7800_ = v_isSharedCheck_7835_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_7797_);
                                        crate::leanh::lean_dec(v_a_7796_);
                                        v___x_7799_ = crate::leanh::lean_box(0);
                                        v_isShared_7800_ = v_isSharedCheck_7835_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_7796_);
                                    v___x_7836_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(
                                        v_expr_7766_,
                                        v_expectedType_7767_,
                                        v_a_7768_,
                                        v_a_7769_,
                                        v_a_7770_,
                                        v_a_7771_,
                                    );
                                    return v___x_7836_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_expectedType_7767_);
                                crate::leanh::lean_dec_ref(v_expr_7766_);
                                v_a_7837_ = crate::leanh::lean_ctor_get(v___x_7795_, 0);
                                v_isSharedCheck_7844_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7795_)) as u8;
                                if v_isSharedCheck_7844_ == 0 {
                                    v___x_7839_ = v___x_7795_;
                                    v_isShared_7840_ = v_isSharedCheck_7844_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7837_);
                                    crate::leanh::lean_dec(v___x_7795_);
                                    v___x_7839_ = crate::leanh::lean_box(0);
                                    v_isShared_7840_ = v_isSharedCheck_7844_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_expectedType_7767_);
                        crate::leanh::lean_dec_ref(v_expr_7766_);
                        v_a_7845_ = crate::leanh::lean_ctor_get(v___x_7791_, 0);
                        v_isSharedCheck_7852_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7791_)) as u8;
                        if v_isSharedCheck_7852_ == 0 {
                            v___x_7847_ = v___x_7791_;
                            v_isShared_7848_ = v_isSharedCheck_7852_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7845_);
                            crate::leanh::lean_dec(v___x_7791_);
                            v___x_7847_ = crate::leanh::lean_box(0);
                            v_isShared_7848_ = v_isSharedCheck_7852_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_7782_ = crate::leanh::lean_box(0);
                v___x_7783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7783_, 0, v_val_7778_);
                crate::leanh::lean_ctor_set(v___x_7783_, 1, v___x_7782_);
                if v_isShared_7781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7780_, 0, v___x_7783_);
                    v___x_7785_ = v___x_7780_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7789_, 0, v___x_7783_);
                    v___x_7785_ = v_reuseFailAlloc_7789_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7776_, 0, v___x_7785_);
                    v___x_7787_ = v___x_7776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7788_, 0, v___x_7785_);
                    v___x_7787_ = v_reuseFailAlloc_7788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7787_;
            }
            5 => {
                crate::leanh::lean_inc(v_a_7771_);
                crate::leanh::lean_inc_ref(v_a_7770_);
                crate::leanh::lean_inc(v_a_7769_);
                crate::leanh::lean_inc_ref(v_a_7768_);
                crate::leanh::lean_inc(v_val_7797_);
                v___x_7801_ =
                    lean_infer_type(v_val_7797_, v_a_7768_, v_a_7769_, v_a_7770_, v_a_7771_);
                if crate::leanh::lean_obj_tag(v___x_7801_) == 0 {
                    v_a_7802_ = crate::leanh::lean_ctor_get(v___x_7801_, 0);
                    crate::leanh::lean_inc(v_a_7802_);
                    crate::leanh::lean_dec_ref_known(v___x_7801_, 1);
                    crate::leanh::lean_inc_ref(v_expectedType_7767_);
                    v___x_7803_ = l_Lean_Meta_isExprDefEq(
                        v_a_7802_,
                        v_expectedType_7767_,
                        v_a_7768_,
                        v_a_7769_,
                        v_a_7770_,
                        v_a_7771_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7803_) == 0 {
                        v_a_7804_ = crate::leanh::lean_ctor_get(v___x_7803_, 0);
                        v_isSharedCheck_7818_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7803_)) as u8;
                        if v_isSharedCheck_7818_ == 0 {
                            v___x_7806_ = v___x_7803_;
                            v_isShared_7807_ = v_isSharedCheck_7818_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7804_);
                            crate::leanh::lean_dec(v___x_7803_);
                            v___x_7806_ = crate::leanh::lean_box(0);
                            v_isShared_7807_ = v_isSharedCheck_7818_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_7799_);
                        crate::leanh::lean_dec(v_val_7797_);
                        crate::leanh::lean_dec_ref(v_expectedType_7767_);
                        crate::leanh::lean_dec_ref(v_expr_7766_);
                        v_a_7819_ = crate::leanh::lean_ctor_get(v___x_7803_, 0);
                        v_isSharedCheck_7826_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7803_)) as u8;
                        if v_isSharedCheck_7826_ == 0 {
                            v___x_7821_ = v___x_7803_;
                            v_isShared_7822_ = v_isSharedCheck_7826_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7819_);
                            crate::leanh::lean_dec(v___x_7803_);
                            v___x_7821_ = crate::leanh::lean_box(0);
                            v_isShared_7822_ = v_isSharedCheck_7826_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7799_);
                    crate::leanh::lean_dec(v_val_7797_);
                    crate::leanh::lean_dec_ref(v_expectedType_7767_);
                    crate::leanh::lean_dec_ref(v_expr_7766_);
                    v_a_7827_ = crate::leanh::lean_ctor_get(v___x_7801_, 0);
                    v_isSharedCheck_7834_ = (!crate::leanh::lean_is_exclusive(v___x_7801_)) as u8;
                    if v_isSharedCheck_7834_ == 0 {
                        v___x_7829_ = v___x_7801_;
                        v_isShared_7830_ = v_isSharedCheck_7834_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7827_);
                        crate::leanh::lean_dec(v___x_7801_);
                        v___x_7829_ = crate::leanh::lean_box(0);
                        v_isShared_7830_ = v_isSharedCheck_7834_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v___x_7808_ = (crate::leanh::lean_unbox(v_a_7804_) as u8);
                crate::leanh::lean_dec(v_a_7804_);
                if v___x_7808_ == 0 {
                    crate::leanh::lean_del_object(v___x_7806_);
                    crate::leanh::lean_del_object(v___x_7799_);
                    crate::leanh::lean_dec(v_val_7797_);
                    v___x_7809_ = l_Lean_Meta_coerceSimpleRecordingNames_x3f(
                        v_expr_7766_,
                        v_expectedType_7767_,
                        v_a_7768_,
                        v_a_7769_,
                        v_a_7770_,
                        v_a_7771_,
                    );
                    return v___x_7809_;
                } else {
                    crate::leanh::lean_dec_ref(v_expectedType_7767_);
                    crate::leanh::lean_dec_ref(v_expr_7766_);
                    v___x_7810_ = crate::leanh::lean_box(0);
                    v___x_7811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7811_, 0, v_val_7797_);
                    crate::leanh::lean_ctor_set(v___x_7811_, 1, v___x_7810_);
                    if v_isShared_7800_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7799_, 0, v___x_7811_);
                        v___x_7813_ = v___x_7799_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7817_, 0, v___x_7811_);
                        v___x_7813_ = v_reuseFailAlloc_7817_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_7807_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7806_, 0, v___x_7813_);
                    v___x_7815_ = v___x_7806_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7816_, 0, v___x_7813_);
                    v___x_7815_ = v_reuseFailAlloc_7816_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7815_;
            }
            9 => {
                if v_isShared_7822_ == 0 {
                    v___x_7824_ = v___x_7821_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7825_, 0, v_a_7819_);
                    v___x_7824_ = v_reuseFailAlloc_7825_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7824_;
            }
            11 => {
                if v_isShared_7830_ == 0 {
                    v___x_7832_ = v___x_7829_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7833_, 0, v_a_7827_);
                    v___x_7832_ = v_reuseFailAlloc_7833_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7832_;
            }
            13 => {
                if v_isShared_7840_ == 0 {
                    v___x_7842_ = v___x_7839_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7843_, 0, v_a_7837_);
                    v___x_7842_ = v_reuseFailAlloc_7843_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7842_;
            }
            15 => {
                if v_isShared_7848_ == 0 {
                    v___x_7850_ = v___x_7847_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7851_, 0, v_a_7845_);
                    v___x_7850_ = v_reuseFailAlloc_7851_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7850_;
            }
            17 => {
                if v_isShared_7857_ == 0 {
                    v___x_7859_ = v___x_7856_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7860_, 0, v_a_7854_);
                    v___x_7859_ = v_reuseFailAlloc_7860_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerceCollectingNames_x3f___boxed(
    mut v_expr_7862_: *mut crate::leanh::LeanObject,
    mut v_expectedType_7863_: *mut crate::leanh::LeanObject,
    mut v_a_7864_: *mut crate::leanh::LeanObject,
    mut v_a_7865_: *mut crate::leanh::LeanObject,
    mut v_a_7866_: *mut crate::leanh::LeanObject,
    mut v_a_7867_: *mut crate::leanh::LeanObject,
    mut v_a_7868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7869_ = l_Lean_Meta_coerceCollectingNames_x3f(
        v_expr_7862_,
        v_expectedType_7863_,
        v_a_7864_,
        v_a_7865_,
        v_a_7866_,
        v_a_7867_,
    );
    crate::leanh::lean_dec(v_a_7867_);
    crate::leanh::lean_dec_ref(v_a_7866_);
    crate::leanh::lean_dec(v_a_7865_);
    crate::leanh::lean_dec_ref(v_a_7864_);
    return v_res_7869_;
}
pub unsafe fn l_Lean_Meta_coerce_x3f(
    mut v_expr_7870_: *mut crate::leanh::LeanObject,
    mut v_expectedType_7871_: *mut crate::leanh::LeanObject,
    mut v_a_7872_: *mut crate::leanh::LeanObject,
    mut v_a_7873_: *mut crate::leanh::LeanObject,
    mut v_a_7874_: *mut crate::leanh::LeanObject,
    mut v_a_7875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7881_: u8 = 0;
    let mut v___x_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7889_: u8 = 0;
    let mut v_fst_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7897_: u8 = 0;
    let mut v___x_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7902_: u8 = 0;
    let mut v_a_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7906_: u8 = 0;
    let mut v___x_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7877_ = l_Lean_Meta_coerceCollectingNames_x3f(
                    v_expr_7870_,
                    v_expectedType_7871_,
                    v_a_7872_,
                    v_a_7873_,
                    v_a_7874_,
                    v_a_7875_,
                );
                if crate::leanh::lean_obj_tag(v___x_7877_) == 0 {
                    v_a_7878_ = crate::leanh::lean_ctor_get(v___x_7877_, 0);
                    v_isSharedCheck_7902_ = (!crate::leanh::lean_is_exclusive(v___x_7877_)) as u8;
                    if v_isSharedCheck_7902_ == 0 {
                        v___x_7880_ = v___x_7877_;
                        v_isShared_7881_ = v_isSharedCheck_7902_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7878_);
                        crate::leanh::lean_dec(v___x_7877_);
                        v___x_7880_ = crate::leanh::lean_box(0);
                        v_isShared_7881_ = v_isSharedCheck_7902_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7903_ = crate::leanh::lean_ctor_get(v___x_7877_, 0);
                    v_isSharedCheck_7910_ = (!crate::leanh::lean_is_exclusive(v___x_7877_)) as u8;
                    if v_isSharedCheck_7910_ == 0 {
                        v___x_7905_ = v___x_7877_;
                        v_isShared_7906_ = v_isSharedCheck_7910_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7903_);
                        crate::leanh::lean_dec(v___x_7877_);
                        v___x_7905_ = crate::leanh::lean_box(0);
                        v_isShared_7906_ = v_isSharedCheck_7910_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_7878_) {
                0 => {
                    v___x_7882_ = crate::leanh::lean_box(0);
                    if v_isShared_7881_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7880_, 0, v___x_7882_);
                        v___x_7884_ = v___x_7880_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7885_, 0, v___x_7882_);
                        v___x_7884_ = v_reuseFailAlloc_7885_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_a_7886_ = crate::leanh::lean_ctor_get(v_a_7878_, 0);
                    v_isSharedCheck_7897_ = (!crate::leanh::lean_is_exclusive(v_a_7878_)) as u8;
                    if v_isSharedCheck_7897_ == 0 {
                        v___x_7888_ = v_a_7878_;
                        v_isShared_7889_ = v_isSharedCheck_7897_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7886_);
                        crate::leanh::lean_dec(v_a_7878_);
                        v___x_7888_ = crate::leanh::lean_box(0);
                        v_isShared_7889_ = v_isSharedCheck_7897_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_7898_ = crate::leanh::lean_box(2);
                    if v_isShared_7881_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7880_, 0, v___x_7898_);
                        v___x_7900_ = v___x_7880_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7901_, 0, v___x_7898_);
                        v___x_7900_ = v_reuseFailAlloc_7901_;
                        state = 6;
                        continue;
                    }
                }
            },
            2 => {
                return v___x_7884_;
            }
            3 => {
                v_fst_7890_ = crate::leanh::lean_ctor_get(v_a_7886_, 0);
                crate::leanh::lean_inc(v_fst_7890_);
                crate::leanh::lean_dec(v_a_7886_);
                if v_isShared_7889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7888_, 0, v_fst_7890_);
                    v___x_7892_ = v___x_7888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7896_, 0, v_fst_7890_);
                    v___x_7892_ = v_reuseFailAlloc_7896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7880_, 0, v___x_7892_);
                    v___x_7894_ = v___x_7880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7895_, 0, v___x_7892_);
                    v___x_7894_ = v_reuseFailAlloc_7895_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7894_;
            }
            6 => {
                return v___x_7900_;
            }
            7 => {
                if v_isShared_7906_ == 0 {
                    v___x_7908_ = v___x_7905_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7909_, 0, v_a_7903_);
                    v___x_7908_ = v_reuseFailAlloc_7909_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_coerce_x3f___boxed(
    mut v_expr_7911_: *mut crate::leanh::LeanObject,
    mut v_expectedType_7912_: *mut crate::leanh::LeanObject,
    mut v_a_7913_: *mut crate::leanh::LeanObject,
    mut v_a_7914_: *mut crate::leanh::LeanObject,
    mut v_a_7915_: *mut crate::leanh::LeanObject,
    mut v_a_7916_: *mut crate::leanh::LeanObject,
    mut v_a_7917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7918_ = l_Lean_Meta_coerce_x3f(
        v_expr_7911_,
        v_expectedType_7912_,
        v_a_7913_,
        v_a_7914_,
        v_a_7915_,
        v_a_7916_,
    );
    crate::leanh::lean_dec(v_a_7916_);
    crate::leanh::lean_dec_ref(v_a_7915_);
    crate::leanh::lean_dec(v_a_7914_);
    crate::leanh::lean_dec_ref(v_a_7913_);
    return v_res_7918_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Coe(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1863807188____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_coeDeclAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_coeDeclAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Coe_0__Lean_Meta_coeDeclAttr___regBuiltin_Lean_Meta_coeDeclAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Coe_0__Lean_Meta_initFn_00___x40_Lean_Meta_Coe_1330821246____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_autoLift = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_autoLift);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Coe(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Coe(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Coe(builtin);
}
