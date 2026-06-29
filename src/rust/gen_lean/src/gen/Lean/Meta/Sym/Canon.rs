// Lean compiler output
// Module: Lean.Meta.Sym.Canon
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.ExprPtr Lean.Meta.SynthInstance Lean.Meta.Sym.SynthInstance Lean.Meta.IntInstTesters Lean.Meta.NatInstTesters Lean.Meta.Sym.Eta Lean.Meta.WHNF Init.Grind.Util
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_eqv___boxed,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hash, l_Lean_Expr_hash___boxed,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isBoolFalse, l_Lean_Expr_isBoolTrue,
    l_Lean_Expr_isConstOf, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_projExpr_x21, l_Lean_Expr_sort___override, l_Lean_Int_mkType, l_Lean_Nat_mkType,
    l_Lean_instInhabitedExpr, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkAppN,
    l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_ParamInfo_isImplicit,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfo;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProp, l_Lean_Meta_isTypeFormer};
use crate::r#gen::Lean::Meta::IntInstTesters::{
    initialize_Lean_Meta_IntInstTesters, l_Lean_Meta_Structural_isInstOfNatInt___redArg,
    runtime_initialize_Lean_Meta_IntInstTesters,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::lean_is_matcher;
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstOfNatNat___redArg,
    runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Offset::{
    l_Lean_Meta_evalNat, l_Lean_Meta_isOffset_x3f, l_Lean_Meta_mkOffset,
};
use crate::r#gen::Lean::Meta::Sym::Eta::{
    initialize_Lean_Meta_Sym_Eta, l_Lean_Meta_Sym_etaReduce, runtime_initialize_Lean_Meta_Sym_Eta,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    initialize_Lean_Meta_Sym_ExprPtr,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    runtime_initialize_Lean_Meta_Sym_ExprPtr,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_getConfig___redArg,
    l_Lean_Meta_Sym_isDefEqI___redArg, l_Lean_Meta_Sym_reportIssue,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::{
    initialize_Lean_Meta_Sym_SynthInstance, l_Lean_Meta_Sym_synthInstanceMeta_x3f,
    runtime_initialize_Lean_Meta_Sym_SynthInstance,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, runtime_initialize_Lean_Meta_SynthInstance,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_reduceMatcher_x3f, l_Lean_Meta_reduceProj_x3f,
    l_Lean_Meta_unfoldDefinition_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_getProjectionFnInfo_x3f;
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_ptr_addr;
use crate::ffi::{lean_expr_eqv, lean_expr_instantiate_rev};
use crate::ffi::lean_infer_type;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 110, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__0_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16563840882919605222 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__1_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12705026313358803449 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__2_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12820753419707900294 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__4_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__5_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__7_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__9_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4607919608188261591 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [67, 97, 110, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__11_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16082358504286671655 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__13_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2251122022426258330 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__14_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8378439444476363067 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__15_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5603484472861445971 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__16_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16442794793046206254 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__17_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10800961243549152282 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__18_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__19_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10155707090415808511 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__20_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__21_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9527747615471850378 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__22_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16493101159247700619 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__23_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__8_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8651052983215277763 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__24_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__10_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15742714460485415006 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__25_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__12_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5942282348343854698 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__26_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1925315962 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,992168563205546145 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__27_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__28_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,928336576844537634 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__29_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__30_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13978976070802251950 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__31_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,639850198844180287 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__0_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__4_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__5_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0_value:
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
    m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1_value:
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
    m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0_value:
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
    m_data: [84, 114, 117, 101, 0],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1_value:
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
            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3_value:
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
            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0_value:
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
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1_value:
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
            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        907667957179513571 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default: u8 = 0;
pub static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult: u8 = 0;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 97, 110, 111, 110, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 97, 110, 111, 110, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 97, 110, 111, 110, 73, 109, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__0_value) as *mut crate::leanh::LeanObject,13428217069302927667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__2_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__2_value) as *mut crate::leanh::LeanObject,16112798088292836701 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__4_value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__5_value) as *mut crate::leanh::LeanObject,9682224670061807480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__7_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__8_value) as *mut crate::leanh::LeanObject,6100819061652633370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__10_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__11_value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__13_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__14_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__16_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__17_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 97, 110, 111, 110, 105, 99, 97, 108, 105, 122, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [10, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [10, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 101, 115, 116, 101, 100, 80, 114, 111, 111, 102, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,1862916703178820790 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [110, 101, 115, 116, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__6_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__0_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__1_value) as *mut crate::leanh::LeanObject,11081308864005098561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__0_value) as *mut crate::leanh::LeanObject,4342836574150310743 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [93, 58, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__0_value) as *mut crate::leanh::LeanObject,105488867511536770 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__2_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 111, 106, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 48, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 80, 114, 111, 106, 33, 73, 109, 112, 108, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_canon___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [115, 121, 109, 32, 99, 97, 110, 111, 110, 0],
    };
static mut l_Lean_Meta_Sym_canon___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_canon___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_;
    v___x_4046_ = 0;
    v___x_4047_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__32_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_;
    v___x_4048_ = l_Lean_registerTraceClass(v___x_4045_, v___x_4046_, v___x_4047_);
    return v___x_4048_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2____boxed(
    mut v_a_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4050_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
    return v_res_4050_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(
    mut v_args_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
    mut v_a_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: u8 = 0;
    let mut v___y_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: u8 = 0;
    let mut v___y_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4085_: u8 = 0;
    let mut v___x_4086_: u8 = 0;
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_a_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut v_args_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_4108_: u8 = 0;
    let mut v___y_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: u8 = 0;
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_a_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: u8 = 0;
    let mut v_modified_4140_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_4144_: u8 = 0;
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4137_ = lean_array_get_size(v_args_4062_);
                v___x_4138_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4139_ = lean_nat_dec_eq(v___x_4137_, v___x_4138_);
                if v___x_4139_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_4062_);
                    state = 1;
                    continue;
                } else {
                    v_modified_4140_ = 0;
                    v___x_4141_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4142_ = lean_array_fget_borrowed(v_args_4062_, v___x_4141_);
                    v___x_4143_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6;
                    v_modified_4144_ = l_Lean_Expr_isAppOf(v___x_4142_, v___x_4143_);
                    if v_modified_4144_ == 0 {
                        v_args_4107_ = v_args_4062_;
                        v_modified_4108_ = v_modified_4140_;
                        v___y_4109_ = v_a_4064_;
                        state = 8;
                        continue;
                    } else {
                        v___x_4145_ = l_Lean_Meta_getNatValue_x3f(
                            v___x_4142_,
                            v_a_4063_,
                            v_a_4064_,
                            v_a_4065_,
                            v_a_4066_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4145_) == 0 {
                            v_a_4146_ = crate::leanh::lean_ctor_get(v___x_4145_, 0);
                            crate::leanh::lean_inc(v_a_4146_);
                            crate::leanh::lean_dec_ref_known(v___x_4145_, 1);
                            if crate::leanh::lean_obj_tag(v_a_4146_) == 1 {
                                v_val_4147_ = crate::leanh::lean_ctor_get(v_a_4146_, 0);
                                crate::leanh::lean_inc(v_val_4147_);
                                crate::leanh::lean_dec_ref_known(v_a_4146_, 1);
                                v___x_4148_ = l_Lean_mkRawNatLit(v_val_4147_);
                                v___x_4149_ =
                                    lean_array_fset(v_args_4062_, v___x_4141_, v___x_4148_);
                                v_args_4107_ = v___x_4149_;
                                v_modified_4108_ = v_modified_4144_;
                                v___y_4109_ = v_a_4064_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_4146_);
                                v_args_4107_ = v_args_4062_;
                                v_modified_4108_ = v_modified_4140_;
                                v___y_4109_ = v_a_4064_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_args_4062_);
                            v_a_4150_ = crate::leanh::lean_ctor_get(v___x_4145_, 0);
                            v_isSharedCheck_4157_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4145_)) as u8;
                            if v_isSharedCheck_4157_ == 0 {
                                v___x_4152_ = v___x_4145_;
                                v_isShared_4153_ = v_isSharedCheck_4157_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4150_);
                                crate::leanh::lean_dec(v___x_4145_);
                                v___x_4152_ = crate::leanh::lean_box(0);
                                v_isShared_4153_ = v_isSharedCheck_4157_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4069_ = crate::leanh::lean_box(0);
                v___x_4070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4070_, 0, v___x_4069_);
                return v___x_4070_;
            }
            2 => {
                if v___y_4072_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4073_);
                    state = 1;
                    continue;
                } else {
                    v___x_4074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4074_, 0, v___y_4073_);
                    v___x_4075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4074_);
                    return v___x_4075_;
                }
            }
            3 => {
                v___x_4081_ =
                    l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_4080_, v___y_4079_);
                if crate::leanh::lean_obj_tag(v___x_4081_) == 0 {
                    v_a_4082_ = crate::leanh::lean_ctor_get(v___x_4081_, 0);
                    v_isSharedCheck_4097_ = (!crate::leanh::lean_is_exclusive(v___x_4081_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4084_ = v___x_4081_;
                        v_isShared_4085_ = v_isSharedCheck_4097_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4082_);
                        crate::leanh::lean_dec(v___x_4081_);
                        v___x_4084_ = crate::leanh::lean_box(0);
                        v_isShared_4085_ = v_isSharedCheck_4097_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4078_);
                    v_a_4098_ = crate::leanh::lean_ctor_get(v___x_4081_, 0);
                    v_isSharedCheck_4105_ = (!crate::leanh::lean_is_exclusive(v___x_4081_)) as u8;
                    if v_isSharedCheck_4105_ == 0 {
                        v___x_4100_ = v___x_4081_;
                        v_isShared_4101_ = v_isSharedCheck_4105_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4098_);
                        crate::leanh::lean_dec(v___x_4081_);
                        v___x_4100_ = crate::leanh::lean_box(0);
                        v_isShared_4101_ = v_isSharedCheck_4105_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4086_ = (crate::leanh::lean_unbox(v_a_4082_) as u8);
                crate::leanh::lean_dec(v_a_4082_);
                if v___x_4086_ == 0 {
                    crate::leanh::lean_del_object(v___x_4084_);
                    v___y_4072_ = v___y_4077_;
                    v___y_4073_ = v___y_4078_;
                    state = 2;
                    continue;
                } else {
                    v___x_4087_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4088_ = lean_array_fget_borrowed(v___y_4078_, v___x_4087_);
                    v___x_4089_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__1;
                    v___x_4090_ = l_Lean_Expr_isConstOf(v___x_4088_, v___x_4089_);
                    if v___x_4090_ == 0 {
                        v___x_4091_ = l_Lean_Int_mkType;
                        v___x_4092_ = lean_array_fset(v___y_4078_, v___x_4087_, v___x_4091_);
                        v___x_4093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
                        if v_isShared_4085_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4093_);
                            v___x_4095_ = v___x_4084_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4096_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
                            v___x_4095_ = v_reuseFailAlloc_4096_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4084_);
                        v___y_4072_ = v___y_4077_;
                        v___y_4073_ = v___y_4078_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4095_;
            }
            6 => {
                if v_isShared_4101_ == 0 {
                    v___x_4103_ = v___x_4100_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
                    v___x_4103_ = v_reuseFailAlloc_4104_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4103_;
            }
            8 => {
                v___x_4110_ = crate::leanh::lean_unsigned_to_nat(2);
                v_inst_4111_ = lean_array_fget_borrowed(v_args_4107_, v___x_4110_);
                crate::leanh::lean_inc(v_inst_4111_);
                v___x_4112_ =
                    l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_inst_4111_, v___y_4109_);
                if crate::leanh::lean_obj_tag(v___x_4112_) == 0 {
                    v_a_4113_ = crate::leanh::lean_ctor_get(v___x_4112_, 0);
                    v_isSharedCheck_4128_ = (!crate::leanh::lean_is_exclusive(v___x_4112_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4115_ = v___x_4112_;
                        v_isShared_4116_ = v_isSharedCheck_4128_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4113_);
                        crate::leanh::lean_dec(v___x_4112_);
                        v___x_4115_ = crate::leanh::lean_box(0);
                        v_isShared_4116_ = v_isSharedCheck_4128_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_4107_);
                    v_a_4129_ = crate::leanh::lean_ctor_get(v___x_4112_, 0);
                    v_isSharedCheck_4136_ = (!crate::leanh::lean_is_exclusive(v___x_4112_)) as u8;
                    if v_isSharedCheck_4136_ == 0 {
                        v___x_4131_ = v___x_4112_;
                        v_isShared_4132_ = v_isSharedCheck_4136_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4129_);
                        crate::leanh::lean_dec(v___x_4112_);
                        v___x_4131_ = crate::leanh::lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4136_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_4117_ = (crate::leanh::lean_unbox(v_a_4113_) as u8);
                crate::leanh::lean_dec(v_a_4113_);
                if v___x_4117_ == 0 {
                    crate::leanh::lean_inc(v_inst_4111_);
                    crate::leanh::lean_del_object(v___x_4115_);
                    v___y_4077_ = v_modified_4108_;
                    v___y_4078_ = v_args_4107_;
                    v___y_4079_ = v___y_4109_;
                    v___y_4080_ = v_inst_4111_;
                    state = 3;
                    continue;
                } else {
                    v___x_4118_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4119_ = lean_array_fget_borrowed(v_args_4107_, v___x_4118_);
                    v___x_4120_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3;
                    v___x_4121_ = l_Lean_Expr_isConstOf(v___x_4119_, v___x_4120_);
                    if v___x_4121_ == 0 {
                        v___x_4122_ = l_Lean_Nat_mkType;
                        v___x_4123_ = lean_array_fset(v_args_4107_, v___x_4118_, v___x_4122_);
                        v___x_4124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4124_, 0, v___x_4123_);
                        if v_isShared_4116_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4115_, 0, v___x_4124_);
                            v___x_4126_ = v___x_4115_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_4127_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
                            v___x_4126_ = v_reuseFailAlloc_4127_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_inst_4111_);
                        crate::leanh::lean_del_object(v___x_4115_);
                        v___y_4077_ = v_modified_4108_;
                        v___y_4078_ = v_args_4107_;
                        v___y_4079_ = v___y_4109_;
                        v___y_4080_ = v_inst_4111_;
                        state = 3;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_4126_;
            }
            11 => {
                if v_isShared_4132_ == 0 {
                    v___x_4134_ = v___x_4131_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
                    v___x_4134_ = v_reuseFailAlloc_4135_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4134_;
            }
            13 => {
                if v_isShared_4153_ == 0 {
                    v___x_4155_ = v___x_4152_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
                    v___x_4155_ = v_reuseFailAlloc_4156_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___boxed(
    mut v_args_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4164_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(
        v_args_4158_,
        v_a_4159_,
        v_a_4160_,
        v_a_4161_,
        v_a_4162_,
    );
    crate::leanh::lean_dec(v_a_4162_);
    crate::leanh::lean_dec_ref(v_a_4161_);
    crate::leanh::lean_dec(v_a_4160_);
    crate::leanh::lean_dec_ref(v_a_4159_);
    return v_res_4164_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(
    mut v_e_4167_: *mut crate::leanh::LeanObject,
    mut v_k_4168_: *mut crate::leanh::LeanObject,
    mut v_a_4169_: u8,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
    mut v_a_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
    mut v_a_4174_: *mut crate::leanh::LeanObject,
    mut v_a_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4196_: u8 = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4208_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v_cache_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4262_: u8 = 0;
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v_cache_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_4169_ == 0 {
                    v___x_4177_ = lean_st_ref_get(v_a_4171_);
                    v_canon_4178_ = crate::leanh::lean_ctor_get(v___x_4177_, 9);
                    crate::leanh::lean_inc_ref(v_canon_4178_);
                    crate::leanh::lean_dec(v___x_4177_);
                    v_cache_4179_ = crate::leanh::lean_ctor_get(v_canon_4178_, 0);
                    crate::leanh::lean_inc_ref(v_cache_4179_);
                    crate::leanh::lean_dec_ref(v_canon_4178_);
                    v___x_4180_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0;
                    v___x_4181_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1;
                    crate::leanh::lean_inc_ref(v_e_4167_);
                    v___x_4182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                        v___x_4180_,
                        v___x_4181_,
                        v_cache_4179_,
                        v_e_4167_,
                    );
                    crate::leanh::lean_dec_ref(v_cache_4179_);
                    if crate::leanh::lean_obj_tag(v___x_4182_) == 1 {
                        crate::leanh::lean_dec_ref(v_k_4168_);
                        crate::leanh::lean_dec_ref(v_e_4167_);
                        v_val_4183_ = crate::leanh::lean_ctor_get(v___x_4182_, 0);
                        v_isSharedCheck_4190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4182_)) as u8;
                        if v_isSharedCheck_4190_ == 0 {
                            v___x_4185_ = v___x_4182_;
                            v_isShared_4186_ = v_isSharedCheck_4190_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4183_);
                            crate::leanh::lean_dec(v___x_4182_);
                            v___x_4185_ = crate::leanh::lean_box(0);
                            v_isShared_4186_ = v_isSharedCheck_4190_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4182_);
                        v___x_4191_ = crate::leanh::lean_box((v_a_4169_) as usize);
                        crate::leanh::lean_inc(v_a_4175_);
                        crate::leanh::lean_inc_ref(v_a_4174_);
                        crate::leanh::lean_inc(v_a_4173_);
                        crate::leanh::lean_inc_ref(v_a_4172_);
                        crate::leanh::lean_inc(v_a_4171_);
                        crate::leanh::lean_inc_ref(v_a_4170_);
                        v___x_4192_ = crate::leanh::lean_apply_8(
                            v_k_4168_,
                            v___x_4191_,
                            v_a_4170_,
                            v_a_4171_,
                            v_a_4172_,
                            v_a_4173_,
                            v_a_4174_,
                            v_a_4175_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4192_) == 0 {
                            v_a_4193_ = crate::leanh::lean_ctor_get(v___x_4192_, 0);
                            v_isSharedCheck_4230_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4192_)) as u8;
                            if v_isSharedCheck_4230_ == 0 {
                                v___x_4195_ = v___x_4192_;
                                v_isShared_4196_ = v_isSharedCheck_4230_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4193_);
                                crate::leanh::lean_dec(v___x_4192_);
                                v___x_4195_ = crate::leanh::lean_box(0);
                                v_isShared_4196_ = v_isSharedCheck_4230_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_4167_);
                            return v___x_4192_;
                        }
                    }
                } else {
                    v___x_4231_ = lean_st_ref_get(v_a_4171_);
                    v_canon_4232_ = crate::leanh::lean_ctor_get(v___x_4231_, 9);
                    crate::leanh::lean_inc_ref(v_canon_4232_);
                    crate::leanh::lean_dec(v___x_4231_);
                    v_cacheInType_4233_ = crate::leanh::lean_ctor_get(v_canon_4232_, 1);
                    crate::leanh::lean_inc_ref(v_cacheInType_4233_);
                    crate::leanh::lean_dec_ref(v_canon_4232_);
                    v___x_4234_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__0;
                    v___x_4235_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___closed__1;
                    crate::leanh::lean_inc_ref(v_e_4167_);
                    v___x_4236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                        v___x_4234_,
                        v___x_4235_,
                        v_cacheInType_4233_,
                        v_e_4167_,
                    );
                    crate::leanh::lean_dec_ref(v_cacheInType_4233_);
                    if crate::leanh::lean_obj_tag(v___x_4236_) == 1 {
                        crate::leanh::lean_dec_ref(v_k_4168_);
                        crate::leanh::lean_dec_ref(v_e_4167_);
                        v_val_4237_ = crate::leanh::lean_ctor_get(v___x_4236_, 0);
                        v_isSharedCheck_4244_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4236_)) as u8;
                        if v_isSharedCheck_4244_ == 0 {
                            v___x_4239_ = v___x_4236_;
                            v_isShared_4240_ = v_isSharedCheck_4244_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4237_);
                            crate::leanh::lean_dec(v___x_4236_);
                            v___x_4239_ = crate::leanh::lean_box(0);
                            v_isShared_4240_ = v_isSharedCheck_4244_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4236_);
                        v___x_4245_ = crate::leanh::lean_box((v_a_4169_) as usize);
                        crate::leanh::lean_inc(v_a_4175_);
                        crate::leanh::lean_inc_ref(v_a_4174_);
                        crate::leanh::lean_inc(v_a_4173_);
                        crate::leanh::lean_inc_ref(v_a_4172_);
                        crate::leanh::lean_inc(v_a_4171_);
                        crate::leanh::lean_inc_ref(v_a_4170_);
                        v___x_4246_ = crate::leanh::lean_apply_8(
                            v_k_4168_,
                            v___x_4245_,
                            v_a_4170_,
                            v_a_4171_,
                            v_a_4172_,
                            v_a_4173_,
                            v_a_4174_,
                            v_a_4175_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4246_) == 0 {
                            v_a_4247_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
                            v_isSharedCheck_4284_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4246_)) as u8;
                            if v_isSharedCheck_4284_ == 0 {
                                v___x_4249_ = v___x_4246_;
                                v_isShared_4250_ = v_isSharedCheck_4284_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4247_);
                                crate::leanh::lean_dec(v___x_4246_);
                                v___x_4249_ = crate::leanh::lean_box(0);
                                v_isShared_4250_ = v_isSharedCheck_4284_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_4167_);
                            return v___x_4246_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4186_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4185_, 0);
                    v___x_4188_ = v___x_4185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_val_4183_);
                    v___x_4188_ = v_reuseFailAlloc_4189_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4188_;
            }
            3 => {
                v___x_4197_ = lean_st_ref_take(v_a_4171_);
                v_canon_4198_ = crate::leanh::lean_ctor_get(v___x_4197_, 9);
                v_share_4199_ = crate::leanh::lean_ctor_get(v___x_4197_, 0);
                v_maxFVar_4200_ = crate::leanh::lean_ctor_get(v___x_4197_, 1);
                v_proofInstInfo_4201_ = crate::leanh::lean_ctor_get(v___x_4197_, 2);
                v_inferType_4202_ = crate::leanh::lean_ctor_get(v___x_4197_, 3);
                v_getLevel_4203_ = crate::leanh::lean_ctor_get(v___x_4197_, 4);
                v_congrInfo_4204_ = crate::leanh::lean_ctor_get(v___x_4197_, 5);
                v_defEqI_4205_ = crate::leanh::lean_ctor_get(v___x_4197_, 6);
                v_extensions_4206_ = crate::leanh::lean_ctor_get(v___x_4197_, 7);
                v_issues_4207_ = crate::leanh::lean_ctor_get(v___x_4197_, 8);
                v_debug_4208_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4197_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v___x_4197_)) as u8;
                if v_isSharedCheck_4229_ == 0 {
                    v___x_4210_ = v___x_4197_;
                    v_isShared_4211_ = v_isSharedCheck_4229_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4198_);
                    crate::leanh::lean_inc(v_issues_4207_);
                    crate::leanh::lean_inc(v_extensions_4206_);
                    crate::leanh::lean_inc(v_defEqI_4205_);
                    crate::leanh::lean_inc(v_congrInfo_4204_);
                    crate::leanh::lean_inc(v_getLevel_4203_);
                    crate::leanh::lean_inc(v_inferType_4202_);
                    crate::leanh::lean_inc(v_proofInstInfo_4201_);
                    crate::leanh::lean_inc(v_maxFVar_4200_);
                    crate::leanh::lean_inc(v_share_4199_);
                    crate::leanh::lean_dec(v___x_4197_);
                    v___x_4210_ = crate::leanh::lean_box(0);
                    v_isShared_4211_ = v_isSharedCheck_4229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_cache_4212_ = crate::leanh::lean_ctor_get(v_canon_4198_, 0);
                v_cacheInType_4213_ = crate::leanh::lean_ctor_get(v_canon_4198_, 1);
                v_isSharedCheck_4228_ = (!crate::leanh::lean_is_exclusive(v_canon_4198_)) as u8;
                if v_isSharedCheck_4228_ == 0 {
                    v___x_4215_ = v_canon_4198_;
                    v_isShared_4216_ = v_isSharedCheck_4228_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_4213_);
                    crate::leanh::lean_inc(v_cache_4212_);
                    crate::leanh::lean_dec(v_canon_4198_);
                    v___x_4215_ = crate::leanh::lean_box(0);
                    v_isShared_4216_ = v_isSharedCheck_4228_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_4193_);
                v___x_4217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4180_,
                    v___x_4181_,
                    v_cache_4212_,
                    v_e_4167_,
                    v_a_4193_,
                );
                if v_isShared_4216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4217_);
                    v___x_4219_ = v___x_4215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_cacheInType_4213_);
                    v___x_4219_ = v_reuseFailAlloc_4227_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4210_, 9, v___x_4219_);
                    v___x_4221_ = v___x_4210_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_share_4199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_maxFVar_4200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 2, v_proofInstInfo_4201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 3, v_inferType_4202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 4, v_getLevel_4203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 5, v_congrInfo_4204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 6, v_defEqI_4205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 7, v_extensions_4206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 8, v_issues_4207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 9, v___x_4219_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4226_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4208_,
                    );
                    v___x_4221_ = v_reuseFailAlloc_4226_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4222_ = lean_st_ref_set(v_a_4171_, v___x_4221_);
                if v_isShared_4196_ == 0 {
                    v___x_4224_ = v___x_4195_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4193_);
                    v___x_4224_ = v_reuseFailAlloc_4225_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4224_;
            }
            9 => {
                if v_isShared_4240_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4239_, 0);
                    v___x_4242_ = v___x_4239_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_val_4237_);
                    v___x_4242_ = v_reuseFailAlloc_4243_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4242_;
            }
            11 => {
                v___x_4251_ = lean_st_ref_take(v_a_4171_);
                v_canon_4252_ = crate::leanh::lean_ctor_get(v___x_4251_, 9);
                v_share_4253_ = crate::leanh::lean_ctor_get(v___x_4251_, 0);
                v_maxFVar_4254_ = crate::leanh::lean_ctor_get(v___x_4251_, 1);
                v_proofInstInfo_4255_ = crate::leanh::lean_ctor_get(v___x_4251_, 2);
                v_inferType_4256_ = crate::leanh::lean_ctor_get(v___x_4251_, 3);
                v_getLevel_4257_ = crate::leanh::lean_ctor_get(v___x_4251_, 4);
                v_congrInfo_4258_ = crate::leanh::lean_ctor_get(v___x_4251_, 5);
                v_defEqI_4259_ = crate::leanh::lean_ctor_get(v___x_4251_, 6);
                v_extensions_4260_ = crate::leanh::lean_ctor_get(v___x_4251_, 7);
                v_issues_4261_ = crate::leanh::lean_ctor_get(v___x_4251_, 8);
                v_debug_4262_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4283_ = (!crate::leanh::lean_is_exclusive(v___x_4251_)) as u8;
                if v_isSharedCheck_4283_ == 0 {
                    v___x_4264_ = v___x_4251_;
                    v_isShared_4265_ = v_isSharedCheck_4283_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4252_);
                    crate::leanh::lean_inc(v_issues_4261_);
                    crate::leanh::lean_inc(v_extensions_4260_);
                    crate::leanh::lean_inc(v_defEqI_4259_);
                    crate::leanh::lean_inc(v_congrInfo_4258_);
                    crate::leanh::lean_inc(v_getLevel_4257_);
                    crate::leanh::lean_inc(v_inferType_4256_);
                    crate::leanh::lean_inc(v_proofInstInfo_4255_);
                    crate::leanh::lean_inc(v_maxFVar_4254_);
                    crate::leanh::lean_inc(v_share_4253_);
                    crate::leanh::lean_dec(v___x_4251_);
                    v___x_4264_ = crate::leanh::lean_box(0);
                    v_isShared_4265_ = v_isSharedCheck_4283_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_cache_4266_ = crate::leanh::lean_ctor_get(v_canon_4252_, 0);
                v_cacheInType_4267_ = crate::leanh::lean_ctor_get(v_canon_4252_, 1);
                v_isSharedCheck_4282_ = (!crate::leanh::lean_is_exclusive(v_canon_4252_)) as u8;
                if v_isSharedCheck_4282_ == 0 {
                    v___x_4269_ = v_canon_4252_;
                    v_isShared_4270_ = v_isSharedCheck_4282_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_4267_);
                    crate::leanh::lean_inc(v_cache_4266_);
                    crate::leanh::lean_dec(v_canon_4252_);
                    v___x_4269_ = crate::leanh::lean_box(0);
                    v_isShared_4270_ = v_isSharedCheck_4282_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc(v_a_4247_);
                v___x_4271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_4234_,
                    v___x_4235_,
                    v_cacheInType_4267_,
                    v_e_4167_,
                    v_a_4247_,
                );
                if v_isShared_4270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4269_, 1, v___x_4271_);
                    v___x_4273_ = v___x_4269_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_cache_4266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 1, v___x_4271_);
                    v___x_4273_ = v_reuseFailAlloc_4281_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4264_, 9, v___x_4273_);
                    v___x_4275_ = v___x_4264_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_share_4253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 1, v_maxFVar_4254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 2, v_proofInstInfo_4255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 3, v_inferType_4256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 4, v_getLevel_4257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 5, v_congrInfo_4258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 6, v_defEqI_4259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 7, v_extensions_4260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 8, v_issues_4261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 9, v___x_4273_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4280_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4262_,
                    );
                    v___x_4275_ = v_reuseFailAlloc_4280_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4276_ = lean_st_ref_set(v_a_4171_, v___x_4275_);
                if v_isShared_4250_ == 0 {
                    v___x_4278_ = v___x_4249_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4247_);
                    v___x_4278_ = v_reuseFailAlloc_4279_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching___boxed(
    mut v_e_4285_: *mut crate::leanh::LeanObject,
    mut v_k_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
    mut v_a_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4295_: u8 = 0;
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4295_ = (crate::leanh::lean_unbox(v_a_4287_) as u8);
    v_res_4296_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_withCaching(
        v_e_4285_,
        v_k_4286_,
        v_a_boxed_4295_,
        v_a_4288_,
        v_a_4289_,
        v_a_4290_,
        v_a_4291_,
        v_a_4292_,
        v_a_4293_,
    );
    crate::leanh::lean_dec(v_a_4293_);
    crate::leanh::lean_dec_ref(v_a_4292_);
    crate::leanh::lean_dec(v_a_4291_);
    crate::leanh::lean_dec_ref(v_a_4290_);
    crate::leanh::lean_dec(v_a_4289_);
    crate::leanh::lean_dec_ref(v_a_4288_);
    return v_res_4296_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(
    mut v_e_4303_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: u8 = 0;
    v___x_4304_ = l_Lean_Expr_cleanupAnnotations(v_e_4303_);
    v___x_4305_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__1;
    v___x_4306_ = l_Lean_Expr_isConstOf(v___x_4304_, v___x_4305_);
    if v___x_4306_ == 0 {
        let mut v___x_4307_: u8 = 0;
        v___x_4307_ = l_Lean_Expr_isApp(v___x_4304_);
        if v___x_4307_ == 0 {
            crate::leanh::lean_dec_ref(v___x_4304_);
            return v___x_4307_;
        } else {
            let mut v_arg_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4310_: u8 = 0;
            v_arg_4308_ = crate::leanh::lean_ctor_get(v___x_4304_, 1);
            crate::leanh::lean_inc_ref(v_arg_4308_);
            v___x_4309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4304_);
            v___x_4310_ = l_Lean_Expr_isApp(v___x_4309_);
            if v___x_4310_ == 0 {
                crate::leanh::lean_dec_ref(v___x_4309_);
                crate::leanh::lean_dec_ref(v_arg_4308_);
                return v___x_4310_;
            } else {
                let mut v_arg_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4313_: u8 = 0;
                v_arg_4311_ = crate::leanh::lean_ctor_get(v___x_4309_, 1);
                crate::leanh::lean_inc_ref(v_arg_4311_);
                v___x_4312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4309_);
                v___x_4313_ = l_Lean_Expr_isApp(v___x_4312_);
                if v___x_4313_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4312_);
                    crate::leanh::lean_dec_ref(v_arg_4311_);
                    crate::leanh::lean_dec_ref(v_arg_4308_);
                    return v___x_4313_;
                } else {
                    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4316_: u8 = 0;
                    v___x_4314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4312_);
                    v___x_4315_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3;
                    v___x_4316_ = l_Lean_Expr_isConstOf(v___x_4314_, v___x_4315_);
                    crate::leanh::lean_dec_ref(v___x_4314_);
                    if v___x_4316_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_4311_);
                        crate::leanh::lean_dec_ref(v_arg_4308_);
                        return v___x_4316_;
                    } else {
                        let mut v___x_4317_: u8 = 0;
                        v___x_4317_ = l_Lean_Expr_isBoolTrue(v_arg_4311_);
                        if v___x_4317_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_4308_);
                            return v___x_4317_;
                        } else {
                            let mut v___x_4318_: u8 = 0;
                            v___x_4318_ = l_Lean_Expr_isBoolTrue(v_arg_4308_);
                            return v___x_4318_;
                        }
                    }
                }
            }
        }
    } else {
        crate::leanh::lean_dec_ref(v___x_4304_);
        return v___x_4306_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___boxed(
    mut v_e_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4320_: u8 = 0;
    let mut v_r_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4320_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(v_e_4319_);
    v_r_4321_ = crate::leanh::lean_box((v_res_4320_) as usize);
    return v_r_4321_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(
    mut v_e_4325_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: u8 = 0;
    v___x_4326_ = l_Lean_Expr_cleanupAnnotations(v_e_4325_);
    v___x_4327_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___closed__1;
    v___x_4328_ = l_Lean_Expr_isConstOf(v___x_4326_, v___x_4327_);
    if v___x_4328_ == 0 {
        let mut v___x_4329_: u8 = 0;
        v___x_4329_ = l_Lean_Expr_isApp(v___x_4326_);
        if v___x_4329_ == 0 {
            crate::leanh::lean_dec_ref(v___x_4326_);
            return v___x_4329_;
        } else {
            let mut v_arg_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4332_: u8 = 0;
            v_arg_4330_ = crate::leanh::lean_ctor_get(v___x_4326_, 1);
            crate::leanh::lean_inc_ref(v_arg_4330_);
            v___x_4331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4326_);
            v___x_4332_ = l_Lean_Expr_isApp(v___x_4331_);
            if v___x_4332_ == 0 {
                crate::leanh::lean_dec_ref(v___x_4331_);
                crate::leanh::lean_dec_ref(v_arg_4330_);
                return v___x_4332_;
            } else {
                let mut v_arg_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4335_: u8 = 0;
                v_arg_4333_ = crate::leanh::lean_ctor_get(v___x_4331_, 1);
                crate::leanh::lean_inc_ref(v_arg_4333_);
                v___x_4334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4331_);
                v___x_4335_ = l_Lean_Expr_isApp(v___x_4334_);
                if v___x_4335_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4334_);
                    crate::leanh::lean_dec_ref(v_arg_4333_);
                    crate::leanh::lean_dec_ref(v_arg_4330_);
                    return v___x_4335_;
                } else {
                    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4338_: u8 = 0;
                    v___x_4336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4334_);
                    v___x_4337_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond___closed__3;
                    v___x_4338_ = l_Lean_Expr_isConstOf(v___x_4336_, v___x_4337_);
                    crate::leanh::lean_dec_ref(v___x_4336_);
                    if v___x_4338_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_4333_);
                        crate::leanh::lean_dec_ref(v_arg_4330_);
                        return v___x_4338_;
                    } else {
                        let mut v___x_4339_: u8 = 0;
                        v___x_4339_ = l_Lean_Expr_isBoolFalse(v_arg_4333_);
                        if v___x_4339_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_4330_);
                            return v___x_4339_;
                        } else {
                            let mut v___x_4340_: u8 = 0;
                            v___x_4340_ = l_Lean_Expr_isBoolTrue(v_arg_4330_);
                            return v___x_4340_;
                        }
                    }
                }
            }
        }
    } else {
        crate::leanh::lean_dec_ref(v___x_4326_);
        return v___x_4328_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond___boxed(
    mut v_e_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4342_: u8 = 0;
    let mut v_r_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(v_e_4341_);
    v_r_4343_ = crate::leanh::lean_box((v_res_4342_) as usize);
    return v_r_4343_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(
    mut v_x_4344_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_4344_ {
        0 => {
            let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4345_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4345_;
        }
        1 => {
            let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4346_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4346_;
        }
        2 => {
            let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4347_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4347_;
        }
        _ => {
            let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4348_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_4348_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx___boxed(
    mut v_x_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4350_: u8 = 0;
    let mut v_res_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4350_ = (crate::leanh::lean_unbox(v_x_4349_) as u8);
    v_res_4351_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(
        v_x_boxed_4350_,
    );
    return v_res_4351_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(
    mut v_x_4352_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorIdx(v_x_4352_);
    return v___x_4353_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx___boxed(
    mut v_x_4354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4355_: u8 = 0;
    let mut v_res_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4355_ = (crate::leanh::lean_unbox(v_x_4354_) as u8);
    v_res_4356_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_toCtorIdx(
            v_x_4__boxed_4355_,
        );
    return v_res_4356_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(
    mut v_k_4357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4357_);
    return v_k_4357_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg___boxed(
    mut v_k_4358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4359_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___redArg(
            v_k_4358_,
        );
    crate::leanh::lean_dec(v_k_4358_);
    return v_res_4359_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(
    mut v_motive_4360_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4361_: *mut crate::leanh::LeanObject,
    mut v_t_4362_: u8,
    mut v_h_4363_: *mut crate::leanh::LeanObject,
    mut v_k_4364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4364_);
    return v_k_4364_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim___boxed(
    mut v_motive_4365_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4366_: *mut crate::leanh::LeanObject,
    mut v_t_4367_: *mut crate::leanh::LeanObject,
    mut v_h_4368_: *mut crate::leanh::LeanObject,
    mut v_k_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4370_: u8 = 0;
    let mut v_res_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4370_ = (crate::leanh::lean_unbox(v_t_4367_) as u8);
    v_res_4371_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_ctorElim(
        v_motive_4365_,
        v_ctorIdx_4366_,
        v_t_boxed_4370_,
        v_h_4368_,
        v_k_4369_,
    );
    crate::leanh::lean_dec(v_k_4369_);
    crate::leanh::lean_dec(v_ctorIdx_4366_);
    return v_res_4371_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(
    mut v_canonType_4372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_canonType_4372_);
    return v_canonType_4372_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(
    mut v_canonType_4373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4374_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_4373_);
    crate::leanh::lean_dec(v_canonType_4373_);
    return v_res_4374_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(
    mut v_motive_4375_: *mut crate::leanh::LeanObject,
    mut v_t_4376_: u8,
    mut v_h_4377_: *mut crate::leanh::LeanObject,
    mut v_canonType_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_canonType_4378_);
    return v_canonType_4378_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim___boxed(
    mut v_motive_4379_: *mut crate::leanh::LeanObject,
    mut v_t_4380_: *mut crate::leanh::LeanObject,
    mut v_h_4381_: *mut crate::leanh::LeanObject,
    mut v_canonType_4382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4383_: u8 = 0;
    let mut v_res_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4383_ = (crate::leanh::lean_unbox(v_t_4380_) as u8);
    v_res_4384_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonType_elim(
            v_motive_4379_,
            v_t_boxed_4383_,
            v_h_4381_,
            v_canonType_4382_,
        );
    crate::leanh::lean_dec(v_canonType_4382_);
    return v_res_4384_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(
    mut v_canonInst_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_canonInst_4385_);
    return v_canonInst_4385_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(
    mut v_canonInst_4386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_4386_);
    crate::leanh::lean_dec(v_canonInst_4386_);
    return v_res_4387_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(
    mut v_motive_4388_: *mut crate::leanh::LeanObject,
    mut v_t_4389_: u8,
    mut v_h_4390_: *mut crate::leanh::LeanObject,
    mut v_canonInst_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_canonInst_4391_);
    return v_canonInst_4391_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim___boxed(
    mut v_motive_4392_: *mut crate::leanh::LeanObject,
    mut v_t_4393_: *mut crate::leanh::LeanObject,
    mut v_h_4394_: *mut crate::leanh::LeanObject,
    mut v_canonInst_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4396_: u8 = 0;
    let mut v_res_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4396_ = (crate::leanh::lean_unbox(v_t_4393_) as u8);
    v_res_4397_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonInst_elim(
            v_motive_4392_,
            v_t_boxed_4396_,
            v_h_4394_,
            v_canonInst_4395_,
        );
    crate::leanh::lean_dec(v_canonInst_4395_);
    return v_res_4397_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(
    mut v_canonImplicit_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_canonImplicit_4398_);
    return v_canonImplicit_4398_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(
    mut v_canonImplicit_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4400_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_4399_);
    crate::leanh::lean_dec(v_canonImplicit_4399_);
    return v_res_4400_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(
    mut v_motive_4401_: *mut crate::leanh::LeanObject,
    mut v_t_4402_: u8,
    mut v_h_4403_: *mut crate::leanh::LeanObject,
    mut v_canonImplicit_4404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_canonImplicit_4404_);
    return v_canonImplicit_4404_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim___boxed(
    mut v_motive_4405_: *mut crate::leanh::LeanObject,
    mut v_t_4406_: *mut crate::leanh::LeanObject,
    mut v_h_4407_: *mut crate::leanh::LeanObject,
    mut v_canonImplicit_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4409_: u8 = 0;
    let mut v_res_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4409_ = (crate::leanh::lean_unbox(v_t_4406_) as u8);
    v_res_4410_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_canonImplicit_elim(
            v_motive_4405_,
            v_t_boxed_4409_,
            v_h_4407_,
            v_canonImplicit_4408_,
        );
    crate::leanh::lean_dec(v_canonImplicit_4408_);
    return v_res_4410_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(
    mut v_visit_4411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_visit_4411_);
    return v_visit_4411_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg___boxed(
    mut v_visit_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4413_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_4412_);
    crate::leanh::lean_dec(v_visit_4412_);
    return v_res_4413_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(
    mut v_motive_4414_: *mut crate::leanh::LeanObject,
    mut v_t_4415_: u8,
    mut v_h_4416_: *mut crate::leanh::LeanObject,
    mut v_visit_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_visit_4417_);
    return v_visit_4417_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim___boxed(
    mut v_motive_4418_: *mut crate::leanh::LeanObject,
    mut v_t_4419_: *mut crate::leanh::LeanObject,
    mut v_h_4420_: *mut crate::leanh::LeanObject,
    mut v_visit_4421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4422_: u8 = 0;
    let mut v_res_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4422_ = (crate::leanh::lean_unbox(v_t_4419_) as u8);
    v_res_4423_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_ShouldCanonResult_visit_elim(
            v_motive_4418_,
            v_t_boxed_4422_,
            v_h_4420_,
            v_visit_4421_,
        );
    crate::leanh::lean_dec(v_visit_4421_);
    return v_res_4423_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default() -> u8 {
    let mut v___x_4424_: u8 = 0;
    v___x_4424_ = 0;
    return v___x_4424_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult()
-> u8 {
    let mut v___x_4425_: u8 = 0;
    v___x_4425_ = 0;
    return v___x_4425_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(
    mut v_r_4438_: u8,
    mut v_x_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_r_4438_ {
        0 => {
            let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4440_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1;
            return v___x_4440_;
        }
        1 => {
            let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4441_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3;
            return v___x_4441_;
        }
        2 => {
            let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4442_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5;
            return v___x_4442_;
        }
        _ => {
            let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4443_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7;
            return v___x_4443_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___boxed(
    mut v_r_4444_: *mut crate::leanh::LeanObject,
    mut v_x_4445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_boxed_4446_: u8 = 0;
    let mut v_res_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_4446_ = (crate::leanh::lean_unbox(v_r_4444_) as u8);
    v_res_4447_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0(
            v_r_boxed_4446_,
            v_x_4445_,
        );
    crate::leanh::lean_dec(v_x_4445_);
    return v_res_4447_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(
    mut v_pinfos_4450_: *mut crate::leanh::LeanObject,
    mut v_i_4451_: *mut crate::leanh::LeanObject,
    mut v_arg_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
    mut v_a_4454_: *mut crate::leanh::LeanObject,
    mut v_a_4455_: *mut crate::leanh::LeanObject,
    mut v_a_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v___x_4468_: u8 = 0;
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4473_: u8 = 0;
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: u8 = 0;
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut v_a_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4503_: u8 = 0;
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4507_: u8 = 0;
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: u8 = 0;
    let mut v_pinfo_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_4511_: u8 = 0;
    let mut v_isProp_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: u8 = 0;
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v___x_4539_: u8 = 0;
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4508_ = lean_array_get_size(v_pinfos_4450_);
                v___x_4509_ = lean_nat_dec_lt(v_i_4451_, v___x_4508_);
                if v___x_4509_ == 0 {
                    v___y_4459_ = v_a_4453_;
                    v___y_4460_ = v_a_4454_;
                    v___y_4461_ = v_a_4455_;
                    v___y_4462_ = v_a_4456_;
                    state = 1;
                    continue;
                } else {
                    v_pinfo_4510_ = lean_array_fget_borrowed(v_pinfos_4450_, v_i_4451_);
                    v_isInstance_4511_ = crate::leanh::lean_ctor_get_uint8(
                        v_pinfo_4510_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                    );
                    if v_isInstance_4511_ == 0 {
                        v_isProp_4512_ = crate::leanh::lean_ctor_get_uint8(
                            v_pinfo_4510_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                        );
                        if v_isProp_4512_ == 0 {
                            v___x_4513_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_4510_);
                            if v___x_4513_ == 0 {
                                v___y_4459_ = v_a_4453_;
                                v___y_4460_ = v_a_4454_;
                                v___y_4461_ = v_a_4455_;
                                v___y_4462_ = v_a_4456_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4514_ = l_Lean_Meta_isTypeFormer(
                                    v_arg_4452_,
                                    v_a_4453_,
                                    v_a_4454_,
                                    v_a_4455_,
                                    v_a_4456_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4514_) == 0 {
                                    v_a_4515_ = crate::leanh::lean_ctor_get(v___x_4514_, 0);
                                    v_isSharedCheck_4530_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4514_)) as u8;
                                    if v_isSharedCheck_4530_ == 0 {
                                        v___x_4517_ = v___x_4514_;
                                        v_isShared_4518_ = v_isSharedCheck_4530_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4515_);
                                        crate::leanh::lean_dec(v___x_4514_);
                                        v___x_4517_ = crate::leanh::lean_box(0);
                                        v_isShared_4518_ = v_isSharedCheck_4530_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4514_, 0);
                                    v_isSharedCheck_4538_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4514_)) as u8;
                                    if v_isSharedCheck_4538_ == 0 {
                                        v___x_4533_ = v___x_4514_;
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4531_);
                                        crate::leanh::lean_dec(v___x_4514_);
                                        v___x_4533_ = crate::leanh::lean_box(0);
                                        v_isShared_4534_ = v_isSharedCheck_4538_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_4452_);
                            v___x_4539_ = 3;
                            v___x_4540_ = crate::leanh::lean_box((v___x_4539_) as usize);
                            v___x_4541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4541_, 0, v___x_4540_);
                            return v___x_4541_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_4452_);
                        v___x_4542_ = 1;
                        v___x_4543_ = crate::leanh::lean_box((v___x_4542_) as usize);
                        v___x_4544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4544_, 0, v___x_4543_);
                        return v___x_4544_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_arg_4452_);
                v___x_4463_ = l_Lean_Meta_isProp(
                    v_arg_4452_,
                    v___y_4459_,
                    v___y_4460_,
                    v___y_4461_,
                    v___y_4462_,
                );
                if crate::leanh::lean_obj_tag(v___x_4463_) == 0 {
                    v_a_4464_ = crate::leanh::lean_ctor_get(v___x_4463_, 0);
                    v_isSharedCheck_4499_ = (!crate::leanh::lean_is_exclusive(v___x_4463_)) as u8;
                    if v_isSharedCheck_4499_ == 0 {
                        v___x_4466_ = v___x_4463_;
                        v_isShared_4467_ = v_isSharedCheck_4499_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4464_);
                        crate::leanh::lean_dec(v___x_4463_);
                        v___x_4466_ = crate::leanh::lean_box(0);
                        v_isShared_4467_ = v_isSharedCheck_4499_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_4452_);
                    v_a_4500_ = crate::leanh::lean_ctor_get(v___x_4463_, 0);
                    v_isSharedCheck_4507_ = (!crate::leanh::lean_is_exclusive(v___x_4463_)) as u8;
                    if v_isSharedCheck_4507_ == 0 {
                        v___x_4502_ = v___x_4463_;
                        v_isShared_4503_ = v_isSharedCheck_4507_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4500_);
                        crate::leanh::lean_dec(v___x_4463_);
                        v___x_4502_ = crate::leanh::lean_box(0);
                        v_isShared_4503_ = v_isSharedCheck_4507_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4468_ = (crate::leanh::lean_unbox(v_a_4464_) as u8);
                crate::leanh::lean_dec(v_a_4464_);
                if v___x_4468_ == 0 {
                    crate::leanh::lean_del_object(v___x_4466_);
                    v___x_4469_ = l_Lean_Meta_isTypeFormer(
                        v_arg_4452_,
                        v___y_4459_,
                        v___y_4460_,
                        v___y_4461_,
                        v___y_4462_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4469_) == 0 {
                        v_a_4470_ = crate::leanh::lean_ctor_get(v___x_4469_, 0);
                        v_isSharedCheck_4485_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4469_)) as u8;
                        if v_isSharedCheck_4485_ == 0 {
                            v___x_4472_ = v___x_4469_;
                            v_isShared_4473_ = v_isSharedCheck_4485_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4470_);
                            crate::leanh::lean_dec(v___x_4469_);
                            v___x_4472_ = crate::leanh::lean_box(0);
                            v_isShared_4473_ = v_isSharedCheck_4485_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4469_, 0);
                        v_isSharedCheck_4493_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4469_)) as u8;
                        if v_isSharedCheck_4493_ == 0 {
                            v___x_4488_ = v___x_4469_;
                            v_isShared_4489_ = v_isSharedCheck_4493_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4486_);
                            crate::leanh::lean_dec(v___x_4469_);
                            v___x_4488_ = crate::leanh::lean_box(0);
                            v_isShared_4489_ = v_isSharedCheck_4493_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_4452_);
                    v___x_4494_ = 3;
                    v___x_4495_ = crate::leanh::lean_box((v___x_4494_) as usize);
                    if v_isShared_4467_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4466_, 0, v___x_4495_);
                        v___x_4497_ = v___x_4466_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
                        v___x_4497_ = v_reuseFailAlloc_4498_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4474_ = (crate::leanh::lean_unbox(v_a_4470_) as u8);
                crate::leanh::lean_dec(v_a_4470_);
                if v___x_4474_ == 0 {
                    v___x_4475_ = 3;
                    v___x_4476_ = crate::leanh::lean_box((v___x_4475_) as usize);
                    if v_isShared_4473_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4472_, 0, v___x_4476_);
                        v___x_4478_ = v___x_4472_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
                        v___x_4478_ = v_reuseFailAlloc_4479_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4480_ = 0;
                    v___x_4481_ = crate::leanh::lean_box((v___x_4480_) as usize);
                    if v_isShared_4473_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4472_, 0, v___x_4481_);
                        v___x_4483_ = v___x_4472_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
                        v___x_4483_ = v_reuseFailAlloc_4484_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4478_;
            }
            5 => {
                return v___x_4483_;
            }
            6 => {
                if v_isShared_4489_ == 0 {
                    v___x_4491_ = v___x_4488_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
                    v___x_4491_ = v_reuseFailAlloc_4492_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4491_;
            }
            8 => {
                return v___x_4497_;
            }
            9 => {
                if v_isShared_4503_ == 0 {
                    v___x_4505_ = v___x_4502_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
                    v___x_4505_ = v_reuseFailAlloc_4506_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4505_;
            }
            11 => {
                v___x_4519_ = (crate::leanh::lean_unbox(v_a_4515_) as u8);
                crate::leanh::lean_dec(v_a_4515_);
                if v___x_4519_ == 0 {
                    v___x_4520_ = 2;
                    v___x_4521_ = crate::leanh::lean_box((v___x_4520_) as usize);
                    if v_isShared_4518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4517_, 0, v___x_4521_);
                        v___x_4523_ = v___x_4517_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4521_);
                        v___x_4523_ = v_reuseFailAlloc_4524_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_4525_ = 0;
                    v___x_4526_ = crate::leanh::lean_box((v___x_4525_) as usize);
                    if v_isShared_4518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4517_, 0, v___x_4526_);
                        v___x_4528_ = v___x_4517_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4526_);
                        v___x_4528_ = v_reuseFailAlloc_4529_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_4523_;
            }
            13 => {
                return v___x_4528_;
            }
            14 => {
                if v_isShared_4534_ == 0 {
                    v___x_4536_ = v___x_4533_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon___boxed(
    mut v_pinfos_4545_: *mut crate::leanh::LeanObject,
    mut v_i_4546_: *mut crate::leanh::LeanObject,
    mut v_arg_4547_: *mut crate::leanh::LeanObject,
    mut v_a_4548_: *mut crate::leanh::LeanObject,
    mut v_a_4549_: *mut crate::leanh::LeanObject,
    mut v_a_4550_: *mut crate::leanh::LeanObject,
    mut v_a_4551_: *mut crate::leanh::LeanObject,
    mut v_a_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4553_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(
        v_pinfos_4545_,
        v_i_4546_,
        v_arg_4547_,
        v_a_4548_,
        v_a_4549_,
        v_a_4550_,
        v_a_4551_,
    );
    crate::leanh::lean_dec(v_a_4551_);
    crate::leanh::lean_dec_ref(v_a_4550_);
    crate::leanh::lean_dec(v_a_4549_);
    crate::leanh::lean_dec_ref(v_a_4548_);
    crate::leanh::lean_dec(v_i_4546_);
    crate::leanh::lean_dec_ref(v_pinfos_4545_);
    return v_res_4553_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4554_ = crate::leanh::lean_box(0);
    v_dummy_4555_ = l_Lean_Expr_sort___override(v___x_4554_);
    return v_dummy_4555_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(
    mut v_info_4556_: *mut crate::leanh::LeanObject,
    mut v_e_4557_: *mut crate::leanh::LeanObject,
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_a_4560_: *mut crate::leanh::LeanObject,
    mut v_a_4561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fromClass_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v_val_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4575_: u8 = 0;
    let mut v_val_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v_dummy_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut v_isSharedCheck_4594_: u8 = 0;
    let mut v_unused_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fromClass_4563_ = crate::leanh::lean_ctor_get_uint8(
                    v_info_4556_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_fromClass_4563_ == 0 {
                    v___x_4564_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_e_4557_,
                        v_fromClass_4563_,
                        v_a_4558_,
                        v_a_4559_,
                        v_a_4560_,
                        v_a_4561_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4564_) == 0 {
                        v_a_4565_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                        v_isSharedCheck_4600_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4564_)) as u8;
                        if v_isSharedCheck_4600_ == 0 {
                            v___x_4567_ = v___x_4564_;
                            v_isShared_4568_ = v_isSharedCheck_4600_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4565_);
                            crate::leanh::lean_dec(v___x_4564_);
                            v___x_4567_ = crate::leanh::lean_box(0);
                            v_isShared_4568_ = v_isSharedCheck_4600_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4564_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4557_);
                    v___x_4601_ = crate::leanh::lean_box(0);
                    v___x_4602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4602_, 0, v___x_4601_);
                    return v___x_4602_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4565_) == 1 {
                    crate::leanh::lean_del_object(v___x_4567_);
                    v_val_4569_ = crate::leanh::lean_ctor_get(v_a_4565_, 0);
                    crate::leanh::lean_inc(v_val_4569_);
                    crate::leanh::lean_dec_ref_known(v_a_4565_, 1);
                    v___x_4570_ = l_Lean_Expr_getAppFn(v_val_4569_);
                    v___x_4571_ = l_Lean_Meta_reduceProj_x3f(
                        v___x_4570_,
                        v_a_4558_,
                        v_a_4559_,
                        v_a_4560_,
                        v_a_4561_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4571_) == 0 {
                        v_a_4572_ = crate::leanh::lean_ctor_get(v___x_4571_, 0);
                        crate::leanh::lean_inc(v_a_4572_);
                        if crate::leanh::lean_obj_tag(v_a_4572_) == 0 {
                            crate::leanh::lean_dec(v_val_4569_);
                            return v___x_4571_;
                        } else {
                            v_isSharedCheck_4594_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4571_)) as u8;
                            if v_isSharedCheck_4594_ == 0 {
                                v_unused_4595_ = crate::leanh::lean_ctor_get(v___x_4571_, 0);
                                crate::leanh::lean_dec(v_unused_4595_);
                                v___x_4574_ = v___x_4571_;
                                v_isShared_4575_ = v_isSharedCheck_4594_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4571_);
                                v___x_4574_ = crate::leanh::lean_box(0);
                                v_isShared_4575_ = v_isSharedCheck_4594_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4569_);
                        return v___x_4571_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4565_);
                    v___x_4596_ = crate::leanh::lean_box(0);
                    if v_isShared_4568_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4567_, 0, v___x_4596_);
                        v___x_4598_ = v___x_4567_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
                        v___x_4598_ = v_reuseFailAlloc_4599_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_val_4576_ = crate::leanh::lean_ctor_get(v_a_4572_, 0);
                v_isSharedCheck_4593_ = (!crate::leanh::lean_is_exclusive(v_a_4572_)) as u8;
                if v_isSharedCheck_4593_ == 0 {
                    v___x_4578_ = v_a_4572_;
                    v_isShared_4579_ = v_isSharedCheck_4593_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_4576_);
                    crate::leanh::lean_dec(v_a_4572_);
                    v___x_4578_ = crate::leanh::lean_box(0);
                    v_isShared_4579_ = v_isSharedCheck_4593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_dummy_4580_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
                v_nargs_4581_ = l_Lean_Expr_getAppNumArgs(v_val_4569_);
                crate::leanh::lean_inc(v_nargs_4581_);
                v___x_4582_ = lean_mk_array(v_nargs_4581_, v_dummy_4580_);
                v___x_4583_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4584_ = lean_nat_sub(v_nargs_4581_, v___x_4583_);
                crate::leanh::lean_dec(v_nargs_4581_);
                v___x_4585_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_val_4569_,
                    v___x_4582_,
                    v___x_4584_,
                );
                v___x_4586_ = l_Lean_mkAppN(v_val_4576_, v___x_4585_);
                crate::leanh::lean_dec_ref(v___x_4585_);
                if v_isShared_4579_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4578_, 0, v___x_4586_);
                    v___x_4588_ = v___x_4578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4586_);
                    v___x_4588_ = v_reuseFailAlloc_4592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4574_, 0, v___x_4588_);
                    v___x_4590_ = v___x_4574_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4591_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4588_);
                    v___x_4590_ = v_reuseFailAlloc_4591_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4590_;
            }
            6 => {
                return v___x_4598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___boxed(
    mut v_info_4603_: *mut crate::leanh::LeanObject,
    mut v_e_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_a_4606_: *mut crate::leanh::LeanObject,
    mut v_a_4607_: *mut crate::leanh::LeanObject,
    mut v_a_4608_: *mut crate::leanh::LeanObject,
    mut v_a_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4610_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(
        v_info_4603_,
        v_e_4604_,
        v_a_4605_,
        v_a_4606_,
        v_a_4607_,
        v_a_4608_,
    );
    crate::leanh::lean_dec(v_a_4608_);
    crate::leanh::lean_dec_ref(v_a_4607_);
    crate::leanh::lean_dec(v_a_4606_);
    crate::leanh::lean_dec_ref(v_a_4605_);
    crate::leanh::lean_dec_ref(v_info_4603_);
    return v_res_4610_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(
    mut v_info_4611_: *mut crate::leanh::LeanObject,
    mut v_e_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_a_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
    mut v_a_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(
        v_info_4611_,
        v_e_4612_,
        v_a_4615_,
        v_a_4616_,
        v_a_4617_,
        v_a_4618_,
    );
    return v___x_4620_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___boxed(
    mut v_info_4621_: *mut crate::leanh::LeanObject,
    mut v_e_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_a_4626_: *mut crate::leanh::LeanObject,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
    mut v_a_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f(
        v_info_4621_,
        v_e_4622_,
        v_a_4623_,
        v_a_4624_,
        v_a_4625_,
        v_a_4626_,
        v_a_4627_,
        v_a_4628_,
    );
    crate::leanh::lean_dec(v_a_4628_);
    crate::leanh::lean_dec_ref(v_a_4627_);
    crate::leanh::lean_dec(v_a_4626_);
    crate::leanh::lean_dec_ref(v_a_4625_);
    crate::leanh::lean_dec(v_a_4624_);
    crate::leanh::lean_dec_ref(v_a_4623_);
    crate::leanh::lean_dec_ref(v_info_4621_);
    return v_res_4630_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(
    mut v_e_4631_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: u8 = 0;
    v___x_4632_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__3;
    v___x_4633_ = l_Lean_Expr_isConstOf(v_e_4631_, v___x_4632_);
    return v___x_4633_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat___boxed(
    mut v_e_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4635_: u8 = 0;
    let mut v_r_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4635_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_e_4634_);
    crate::leanh::lean_dec_ref(v_e_4634_);
    v_r_4636_ = crate::leanh::lean_box((v_res_4635_) as usize);
    return v_r_4636_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(
    mut v_e_4670_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: u8 = 0;
    v___x_4671_ = l_Lean_Expr_cleanupAnnotations(v_e_4670_);
    v___x_4672_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__1;
    v___x_4673_ = l_Lean_Expr_isConstOf(v___x_4671_, v___x_4672_);
    if v___x_4673_ == 0 {
        let mut v___x_4674_: u8 = 0;
        v___x_4674_ = l_Lean_Expr_isApp(v___x_4671_);
        if v___x_4674_ == 0 {
            crate::leanh::lean_dec_ref(v___x_4671_);
            return v___x_4674_;
        } else {
            let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4677_: u8 = 0;
            v___x_4675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4671_);
            v___x_4676_ =
                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__3;
            v___x_4677_ = l_Lean_Expr_isConstOf(v___x_4675_, v___x_4676_);
            if v___x_4677_ == 0 {
                let mut v___x_4678_: u8 = 0;
                v___x_4678_ = l_Lean_Expr_isApp(v___x_4675_);
                if v___x_4678_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4675_);
                    return v___x_4678_;
                } else {
                    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4680_: u8 = 0;
                    v___x_4679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4675_);
                    v___x_4680_ = l_Lean_Expr_isApp(v___x_4679_);
                    if v___x_4680_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4679_);
                        return v___x_4680_;
                    } else {
                        let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4682_: u8 = 0;
                        v___x_4681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4679_);
                        v___x_4682_ = l_Lean_Expr_isApp(v___x_4681_);
                        if v___x_4682_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4681_);
                            return v___x_4682_;
                        } else {
                            let mut v___x_4683_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4684_: u8 = 0;
                            v___x_4683_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4681_);
                            v___x_4684_ = l_Lean_Expr_isApp(v___x_4683_);
                            if v___x_4684_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4683_);
                                return v___x_4684_;
                            } else {
                                let mut v___x_4685_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4686_: u8 = 0;
                                v___x_4685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4683_);
                                v___x_4686_ = l_Lean_Expr_isApp(v___x_4685_);
                                if v___x_4686_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_4685_);
                                    return v___x_4686_;
                                } else {
                                    let mut v_arg_4687_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4688_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4689_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4690_: u8 = 0;
                                    v_arg_4687_ = crate::leanh::lean_ctor_get(v___x_4685_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_4687_);
                                    v___x_4688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4685_);
                                    v___x_4689_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__6;
                                    v___x_4690_ = l_Lean_Expr_isConstOf(v___x_4688_, v___x_4689_);
                                    if v___x_4690_ == 0 {
                                        let mut v___x_4691_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_4692_: u8 = 0;
                                        v___x_4691_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__9;
                                        v___x_4692_ =
                                            l_Lean_Expr_isConstOf(v___x_4688_, v___x_4691_);
                                        if v___x_4692_ == 0 {
                                            let mut v___x_4693_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_4694_: u8 = 0;
                                            v___x_4693_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__12;
                                            v___x_4694_ =
                                                l_Lean_Expr_isConstOf(v___x_4688_, v___x_4693_);
                                            if v___x_4694_ == 0 {
                                                let mut v___x_4695_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_4696_: u8 = 0;
                                                v___x_4695_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__15;
                                                v___x_4696_ =
                                                    l_Lean_Expr_isConstOf(v___x_4688_, v___x_4695_);
                                                if v___x_4696_ == 0 {
                                                    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_4698_: u8 = 0;
                                                    v___x_4697_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___closed__18;
                                                    v___x_4698_ = l_Lean_Expr_isConstOf(
                                                        v___x_4688_,
                                                        v___x_4697_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_4688_);
                                                    if v___x_4698_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_4687_);
                                                        return v___x_4698_;
                                                    } else {
                                                        let mut v___x_4699_: u8 = 0;
                                                        v___x_4699_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_4687_);
                                                        crate::leanh::lean_dec_ref(v_arg_4687_);
                                                        return v___x_4699_;
                                                    }
                                                } else {
                                                    let mut v___x_4700_: u8 = 0;
                                                    crate::leanh::lean_dec_ref(v___x_4688_);
                                                    v___x_4700_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_4687_);
                                                    crate::leanh::lean_dec_ref(v_arg_4687_);
                                                    return v___x_4700_;
                                                }
                                            } else {
                                                let mut v___x_4701_: u8 = 0;
                                                crate::leanh::lean_dec_ref(v___x_4688_);
                                                v___x_4701_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_4687_);
                                                crate::leanh::lean_dec_ref(v_arg_4687_);
                                                return v___x_4701_;
                                            }
                                        } else {
                                            let mut v___x_4702_: u8 = 0;
                                            crate::leanh::lean_dec_ref(v___x_4688_);
                                            v___x_4702_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_4687_);
                                            crate::leanh::lean_dec_ref(v_arg_4687_);
                                            return v___x_4702_;
                                        }
                                    } else {
                                        let mut v___x_4703_: u8 = 0;
                                        crate::leanh::lean_dec_ref(v___x_4688_);
                                        v___x_4703_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNat(v_arg_4687_);
                                        crate::leanh::lean_dec_ref(v_arg_4687_);
                                        return v___x_4703_;
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                crate::leanh::lean_dec_ref(v___x_4675_);
                return v___x_4677_;
            }
        }
    } else {
        crate::leanh::lean_dec_ref(v___x_4671_);
        return v___x_4673_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp___boxed(
    mut v_e_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4705_: u8 = 0;
    let mut v_r_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4705_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_4704_);
    v_r_4706_ = crate::leanh::lean_box((v_res_4705_) as usize);
    return v_r_4706_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4708_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__0;
    v___x_4709_ = l_Lean_stringToMessageData(v___x_4708_);
    return v___x_4709_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4711_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__2;
    v___x_4712_ = l_Lean_stringToMessageData(v___x_4711_);
    return v___x_4712_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(
    mut v_e_4713_: *mut crate::leanh::LeanObject,
    mut v_inst_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
    mut v_a_4716_: *mut crate::leanh::LeanObject,
    mut v_a_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4726_: u8 = 0;
    let mut v___x_4727_: u8 = 0;
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4732_: u8 = 0;
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v_unused_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut v_a_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4765_: u8 = 0;
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut v_a_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_4714_);
                crate::leanh::lean_inc_ref(v_e_4713_);
                v___x_4722_ = l_Lean_Meta_Sym_isDefEqI___redArg(
                    v_e_4713_,
                    v_inst_4714_,
                    v_a_4716_,
                    v_a_4717_,
                    v_a_4718_,
                    v_a_4719_,
                    v_a_4720_,
                );
                if crate::leanh::lean_obj_tag(v___x_4722_) == 0 {
                    v_a_4723_ = crate::leanh::lean_ctor_get(v___x_4722_, 0);
                    v_isSharedCheck_4773_ = (!crate::leanh::lean_is_exclusive(v___x_4722_)) as u8;
                    if v_isSharedCheck_4773_ == 0 {
                        v___x_4725_ = v___x_4722_;
                        v_isShared_4726_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4723_);
                        crate::leanh::lean_dec(v___x_4722_);
                        v___x_4725_ = crate::leanh::lean_box(0);
                        v_isShared_4726_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_4714_);
                    crate::leanh::lean_dec_ref(v_e_4713_);
                    v_a_4774_ = crate::leanh::lean_ctor_get(v___x_4722_, 0);
                    v_isSharedCheck_4781_ = (!crate::leanh::lean_is_exclusive(v___x_4722_)) as u8;
                    if v_isSharedCheck_4781_ == 0 {
                        v___x_4776_ = v___x_4722_;
                        v_isShared_4777_ = v_isSharedCheck_4781_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4774_);
                        crate::leanh::lean_dec(v___x_4722_);
                        v___x_4776_ = crate::leanh::lean_box(0);
                        v_isShared_4777_ = v_isSharedCheck_4781_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4727_ = (crate::leanh::lean_unbox(v_a_4723_) as u8);
                crate::leanh::lean_dec(v_a_4723_);
                if v___x_4727_ == 0 {
                    crate::leanh::lean_del_object(v___x_4725_);
                    v___x_4728_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4715_);
                    if crate::leanh::lean_obj_tag(v___x_4728_) == 0 {
                        v_a_4729_ = crate::leanh::lean_ctor_get(v___x_4728_, 0);
                        v_isSharedCheck_4761_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4728_)) as u8;
                        if v_isSharedCheck_4761_ == 0 {
                            v___x_4731_ = v___x_4728_;
                            v_isShared_4732_ = v_isSharedCheck_4761_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4729_);
                            crate::leanh::lean_dec(v___x_4728_);
                            v___x_4731_ = crate::leanh::lean_box(0);
                            v_isShared_4732_ = v_isSharedCheck_4761_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_4714_);
                        crate::leanh::lean_dec_ref(v_e_4713_);
                        v_a_4762_ = crate::leanh::lean_ctor_get(v___x_4728_, 0);
                        v_isSharedCheck_4769_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4728_)) as u8;
                        if v_isSharedCheck_4769_ == 0 {
                            v___x_4764_ = v___x_4728_;
                            v_isShared_4765_ = v_isSharedCheck_4769_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4762_);
                            crate::leanh::lean_dec(v___x_4728_);
                            v___x_4764_ = crate::leanh::lean_box(0);
                            v_isShared_4765_ = v_isSharedCheck_4769_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4713_);
                    if v_isShared_4726_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4725_, 0, v_inst_4714_);
                        v___x_4771_ = v___x_4725_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_inst_4714_);
                        v___x_4771_ = v_reuseFailAlloc_4772_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4733_ = (crate::leanh::lean_unbox(v_a_4729_) as u8);
                crate::leanh::lean_dec(v_a_4729_);
                if v___x_4733_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_4714_);
                    if v_isShared_4732_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4731_, 0, v_e_4713_);
                        v___x_4735_ = v___x_4731_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_e_4713_);
                        v___x_4735_ = v_reuseFailAlloc_4736_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4731_);
                    v___x_4737_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
                    crate::leanh::lean_inc_ref(v_e_4713_);
                    v___x_4738_ = l_Lean_indentExpr(v_e_4713_);
                    v___x_4739_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4739_, 0, v___x_4737_);
                    crate::leanh::lean_ctor_set(v___x_4739_, 1, v___x_4738_);
                    v___x_4740_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__3);
                    v___x_4741_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4741_, 0, v___x_4739_);
                    crate::leanh::lean_ctor_set(v___x_4741_, 1, v___x_4740_);
                    v___x_4742_ = l_Lean_indentExpr(v_inst_4714_);
                    v___x_4743_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4743_, 0, v___x_4741_);
                    crate::leanh::lean_ctor_set(v___x_4743_, 1, v___x_4742_);
                    v___x_4744_ = l_Lean_Meta_Sym_reportIssue(
                        v___x_4743_,
                        v_a_4715_,
                        v_a_4716_,
                        v_a_4717_,
                        v_a_4718_,
                        v_a_4719_,
                        v_a_4720_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4744_) == 0 {
                        v_isSharedCheck_4751_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4751_ == 0 {
                            v_unused_4752_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                            crate::leanh::lean_dec(v_unused_4752_);
                            v___x_4746_ = v___x_4744_;
                            v_isShared_4747_ = v_isSharedCheck_4751_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4744_);
                            v___x_4746_ = crate::leanh::lean_box(0);
                            v_isShared_4747_ = v_isSharedCheck_4751_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4713_);
                        v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4760_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4760_ == 0 {
                            v___x_4755_ = v___x_4744_;
                            v_isShared_4756_ = v_isSharedCheck_4760_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4753_);
                            crate::leanh::lean_dec(v___x_4744_);
                            v___x_4755_ = crate::leanh::lean_box(0);
                            v_isShared_4756_ = v_isSharedCheck_4760_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_4735_;
            }
            4 => {
                if v_isShared_4747_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4746_, 0, v_e_4713_);
                    v___x_4749_ = v___x_4746_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_e_4713_);
                    v___x_4749_ = v_reuseFailAlloc_4750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4749_;
            }
            6 => {
                if v_isShared_4756_ == 0 {
                    v___x_4758_ = v___x_4755_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
                    v___x_4758_ = v_reuseFailAlloc_4759_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4758_;
            }
            8 => {
                if v_isShared_4765_ == 0 {
                    v___x_4767_ = v___x_4764_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
                    v___x_4767_ = v_reuseFailAlloc_4768_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4767_;
            }
            10 => {
                return v___x_4771_;
            }
            11 => {
                if v_isShared_4777_ == 0 {
                    v___x_4779_ = v___x_4776_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
                    v___x_4779_ = v_reuseFailAlloc_4780_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___boxed(
    mut v_e_4782_: *mut crate::leanh::LeanObject,
    mut v_inst_4783_: *mut crate::leanh::LeanObject,
    mut v_a_4784_: *mut crate::leanh::LeanObject,
    mut v_a_4785_: *mut crate::leanh::LeanObject,
    mut v_a_4786_: *mut crate::leanh::LeanObject,
    mut v_a_4787_: *mut crate::leanh::LeanObject,
    mut v_a_4788_: *mut crate::leanh::LeanObject,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4791_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(
        v_e_4782_,
        v_inst_4783_,
        v_a_4784_,
        v_a_4785_,
        v_a_4786_,
        v_a_4787_,
        v_a_4788_,
        v_a_4789_,
    );
    crate::leanh::lean_dec(v_a_4789_);
    crate::leanh::lean_dec_ref(v_a_4788_);
    crate::leanh::lean_dec(v_a_4787_);
    crate::leanh::lean_dec_ref(v_a_4786_);
    crate::leanh::lean_dec(v_a_4785_);
    crate::leanh::lean_dec_ref(v_a_4784_);
    return v_res_4791_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(
    mut v_declName_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = lean_st_ref_get(v___y_4793_);
    v_env_4796_ = crate::leanh::lean_ctor_get(v___x_4795_, 0);
    crate::leanh::lean_inc_ref(v_env_4796_);
    crate::leanh::lean_dec(v___x_4795_);
    v___x_4797_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4796_, v_declName_4792_);
    v___x_4798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4798_, 0, v___x_4797_);
    return v___x_4798_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg___boxed(
    mut v_declName_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_4799_, v___y_4800_);
    crate::leanh::lean_dec(v___y_4800_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(
    mut v_declName_4803_: *mut crate::leanh::LeanObject,
    mut v___y_4804_: u8,
    mut v___y_4805_: *mut crate::leanh::LeanObject,
    mut v___y_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4812_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_4803_, v___y_4810_);
    return v___x_4812_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___boxed(
    mut v_declName_4813_: *mut crate::leanh::LeanObject,
    mut v___y_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4015__boxed_4822_: u8 = 0;
    let mut v_res_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4015__boxed_4822_ = (crate::leanh::lean_unbox(v___y_4814_) as u8);
    v_res_4823_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0(v_declName_4813_, v___y_4015__boxed_4822_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
    crate::leanh::lean_dec(v___y_4820_);
    crate::leanh::lean_dec_ref(v___y_4819_);
    crate::leanh::lean_dec(v___y_4818_);
    crate::leanh::lean_dec_ref(v___y_4817_);
    crate::leanh::lean_dec(v___y_4816_);
    crate::leanh::lean_dec_ref(v___y_4815_);
    return v_res_4823_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(
    mut v_e_4824_: *mut crate::leanh::LeanObject,
    mut v_a_4825_: u8,
    mut v_a_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
    mut v_a_4828_: *mut crate::leanh::LeanObject,
    mut v_a_4829_: *mut crate::leanh::LeanObject,
    mut v_a_4830_: *mut crate::leanh::LeanObject,
    mut v_a_4831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4833_: u8 = 0;
    let mut v_f_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v_val_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4846_: u8 = 0;
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4854_: u8 = 0;
    let mut v_a_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4866_: u8 = 0;
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v_val_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4882_: u8 = 0;
    let mut v_val_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4890_: u8 = 0;
    let mut v_a_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4894_: u8 = 0;
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4898_: u8 = 0;
    let mut v_isSharedCheck_4899_: u8 = 0;
    let mut v_a_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4824_);
                v___x_4833_ =
                    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isNatArithApp(v_e_4824_);
                if v___x_4833_ == 0 {
                    v_f_4834_ = l_Lean_Expr_getAppFn(v_e_4824_);
                    if crate::leanh::lean_obj_tag(v_f_4834_) == 4 {
                        v_declName_4835_ = crate::leanh::lean_ctor_get(v_f_4834_, 0);
                        crate::leanh::lean_inc(v_declName_4835_);
                        crate::leanh::lean_dec_ref_known(v_f_4834_, 2);
                        v___x_4836_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce_spec__0___redArg(v_declName_4835_, v_a_4831_);
                        v_a_4837_ = crate::leanh::lean_ctor_get(v___x_4836_, 0);
                        v_isSharedCheck_4866_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4836_)) as u8;
                        if v_isSharedCheck_4866_ == 0 {
                            v___x_4839_ = v___x_4836_;
                            v_isShared_4840_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4837_);
                            crate::leanh::lean_dec(v___x_4836_);
                            v___x_4839_ = crate::leanh::lean_box(0);
                            v_isShared_4840_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_4834_);
                        v___x_4867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4867_, 0, v_e_4824_);
                        return v___x_4867_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_e_4824_);
                    v___x_4868_ =
                        l_Lean_Meta_evalNat(v_e_4824_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
                    if crate::leanh::lean_obj_tag(v___x_4868_) == 0 {
                        v_a_4869_ = crate::leanh::lean_ctor_get(v___x_4868_, 0);
                        v_isSharedCheck_4899_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4868_)) as u8;
                        if v_isSharedCheck_4899_ == 0 {
                            v___x_4871_ = v___x_4868_;
                            v_isShared_4872_ = v_isSharedCheck_4899_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4869_);
                            crate::leanh::lean_dec(v___x_4868_);
                            v___x_4871_ = crate::leanh::lean_box(0);
                            v_isShared_4872_ = v_isSharedCheck_4899_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4824_);
                        v_a_4900_ = crate::leanh::lean_ctor_get(v___x_4868_, 0);
                        v_isSharedCheck_4907_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4868_)) as u8;
                        if v_isSharedCheck_4907_ == 0 {
                            v___x_4902_ = v___x_4868_;
                            v_isShared_4903_ = v_isSharedCheck_4907_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4900_);
                            crate::leanh::lean_dec(v___x_4868_);
                            v___x_4902_ = crate::leanh::lean_box(0);
                            v_isShared_4903_ = v_isSharedCheck_4907_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4837_) == 1 {
                    crate::leanh::lean_del_object(v___x_4839_);
                    v_val_4841_ = crate::leanh::lean_ctor_get(v_a_4837_, 0);
                    crate::leanh::lean_inc(v_val_4841_);
                    crate::leanh::lean_dec_ref_known(v_a_4837_, 1);
                    crate::leanh::lean_inc_ref(v_e_4824_);
                    v___x_4842_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg(v_val_4841_, v_e_4824_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
                    crate::leanh::lean_dec(v_val_4841_);
                    if crate::leanh::lean_obj_tag(v___x_4842_) == 0 {
                        v_a_4843_ = crate::leanh::lean_ctor_get(v___x_4842_, 0);
                        v_isSharedCheck_4854_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4842_)) as u8;
                        if v_isSharedCheck_4854_ == 0 {
                            v___x_4845_ = v___x_4842_;
                            v_isShared_4846_ = v_isSharedCheck_4854_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4843_);
                            crate::leanh::lean_dec(v___x_4842_);
                            v___x_4845_ = crate::leanh::lean_box(0);
                            v_isShared_4846_ = v_isSharedCheck_4854_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4824_);
                        v_a_4855_ = crate::leanh::lean_ctor_get(v___x_4842_, 0);
                        v_isSharedCheck_4862_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4842_)) as u8;
                        if v_isSharedCheck_4862_ == 0 {
                            v___x_4857_ = v___x_4842_;
                            v_isShared_4858_ = v_isSharedCheck_4862_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4855_);
                            crate::leanh::lean_dec(v___x_4842_);
                            v___x_4857_ = crate::leanh::lean_box(0);
                            v_isShared_4858_ = v_isSharedCheck_4862_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4837_);
                    if v_isShared_4840_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4839_, 0, v_e_4824_);
                        v___x_4864_ = v___x_4839_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_e_4824_);
                        v___x_4864_ = v_reuseFailAlloc_4865_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4843_) == 0 {
                    if v_isShared_4846_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4845_, 0, v_e_4824_);
                        v___x_4848_ = v___x_4845_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_e_4824_);
                        v___x_4848_ = v_reuseFailAlloc_4849_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4824_);
                    v_val_4850_ = crate::leanh::lean_ctor_get(v_a_4843_, 0);
                    crate::leanh::lean_inc(v_val_4850_);
                    crate::leanh::lean_dec_ref_known(v_a_4843_, 1);
                    if v_isShared_4846_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4845_, 0, v_val_4850_);
                        v___x_4852_ = v___x_4845_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_val_4850_);
                        v___x_4852_ = v_reuseFailAlloc_4853_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4848_;
            }
            4 => {
                return v___x_4852_;
            }
            5 => {
                if v_isShared_4858_ == 0 {
                    v___x_4860_ = v___x_4857_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
                    v___x_4860_ = v_reuseFailAlloc_4861_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4860_;
            }
            7 => {
                return v___x_4864_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_4869_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_4824_);
                    v_val_4873_ = crate::leanh::lean_ctor_get(v_a_4869_, 0);
                    crate::leanh::lean_inc(v_val_4873_);
                    crate::leanh::lean_dec_ref_known(v_a_4869_, 1);
                    v___x_4874_ = l_Lean_mkNatLit(v_val_4873_);
                    if v_isShared_4872_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4871_, 0, v___x_4874_);
                        v___x_4876_ = v___x_4871_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4874_);
                        v___x_4876_ = v_reuseFailAlloc_4877_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4871_);
                    crate::leanh::lean_dec(v_a_4869_);
                    crate::leanh::lean_inc_ref(v_e_4824_);
                    v___x_4878_ = l_Lean_Meta_isOffset_x3f(
                        v_e_4824_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4878_) == 0 {
                        v_a_4879_ = crate::leanh::lean_ctor_get(v___x_4878_, 0);
                        v_isSharedCheck_4890_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4878_)) as u8;
                        if v_isSharedCheck_4890_ == 0 {
                            v___x_4881_ = v___x_4878_;
                            v_isShared_4882_ = v_isSharedCheck_4890_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4879_);
                            crate::leanh::lean_dec(v___x_4878_);
                            v___x_4881_ = crate::leanh::lean_box(0);
                            v_isShared_4882_ = v_isSharedCheck_4890_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4824_);
                        v_a_4891_ = crate::leanh::lean_ctor_get(v___x_4878_, 0);
                        v_isSharedCheck_4898_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4878_)) as u8;
                        if v_isSharedCheck_4898_ == 0 {
                            v___x_4893_ = v___x_4878_;
                            v_isShared_4894_ = v_isSharedCheck_4898_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4891_);
                            crate::leanh::lean_dec(v___x_4878_);
                            v___x_4893_ = crate::leanh::lean_box(0);
                            v_isShared_4894_ = v_isSharedCheck_4898_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_4876_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_4879_) == 1 {
                    crate::leanh::lean_del_object(v___x_4881_);
                    crate::leanh::lean_dec_ref(v_e_4824_);
                    v_val_4883_ = crate::leanh::lean_ctor_get(v_a_4879_, 0);
                    crate::leanh::lean_inc(v_val_4883_);
                    crate::leanh::lean_dec_ref_known(v_a_4879_, 1);
                    v_fst_4884_ = crate::leanh::lean_ctor_get(v_val_4883_, 0);
                    crate::leanh::lean_inc(v_fst_4884_);
                    v_snd_4885_ = crate::leanh::lean_ctor_get(v_val_4883_, 1);
                    crate::leanh::lean_inc(v_snd_4885_);
                    crate::leanh::lean_dec(v_val_4883_);
                    v___x_4886_ = l_Lean_Meta_mkOffset(
                        v_fst_4884_,
                        v_snd_4885_,
                        v_a_4828_,
                        v_a_4829_,
                        v_a_4830_,
                        v_a_4831_,
                    );
                    return v___x_4886_;
                } else {
                    crate::leanh::lean_dec(v_a_4879_);
                    if v_isShared_4882_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4881_, 0, v_e_4824_);
                        v___x_4888_ = v___x_4881_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_e_4824_);
                        v___x_4888_ = v_reuseFailAlloc_4889_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_4888_;
            }
            12 => {
                if v_isShared_4894_ == 0 {
                    v___x_4896_ = v___x_4893_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4897_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
                    v___x_4896_ = v_reuseFailAlloc_4897_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4896_;
            }
            14 => {
                if v_isShared_4903_ == 0 {
                    v___x_4905_ = v___x_4902_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
                    v___x_4905_ = v_reuseFailAlloc_4906_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce___boxed(
    mut v_e_4908_: *mut crate::leanh::LeanObject,
    mut v_a_4909_: *mut crate::leanh::LeanObject,
    mut v_a_4910_: *mut crate::leanh::LeanObject,
    mut v_a_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
    mut v_a_4913_: *mut crate::leanh::LeanObject,
    mut v_a_4914_: *mut crate::leanh::LeanObject,
    mut v_a_4915_: *mut crate::leanh::LeanObject,
    mut v_a_4916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4917_: u8 = 0;
    let mut v_res_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4917_ = (crate::leanh::lean_unbox(v_a_4909_) as u8);
    v_res_4918_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(
        v_e_4908_,
        v_a_boxed_4917_,
        v_a_4910_,
        v_a_4911_,
        v_a_4912_,
        v_a_4913_,
        v_a_4914_,
        v_a_4915_,
    );
    crate::leanh::lean_dec(v_a_4915_);
    crate::leanh::lean_dec_ref(v_a_4914_);
    crate::leanh::lean_dec(v_a_4913_);
    crate::leanh::lean_dec_ref(v_a_4912_);
    crate::leanh::lean_dec(v_a_4911_);
    crate::leanh::lean_dec_ref(v_a_4910_);
    return v_res_4918_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__0;
    v___x_4921_ = l_Lean_stringToMessageData(v___x_4920_);
    return v___x_4921_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(
    mut v_e_4922_: *mut crate::leanh::LeanObject,
    mut v_type_4923_: *mut crate::leanh::LeanObject,
    mut v_report_4924_: u8,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v_a_4928_: *mut crate::leanh::LeanObject,
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_a_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v_val_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4961_: u8 = 0;
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_unused_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4970_: u8 = 0;
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4974_: u8 = 0;
    let mut v_isSharedCheck_4975_: u8 = 0;
    let mut v_a_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_a_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_4923_);
                v___x_4932_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_4923_,
                    v_a_4927_,
                    v_a_4928_,
                    v_a_4929_,
                    v_a_4930_,
                );
                if crate::leanh::lean_obj_tag(v___x_4932_) == 0 {
                    v_a_4933_ = crate::leanh::lean_ctor_get(v___x_4932_, 0);
                    v_isSharedCheck_4984_ = (!crate::leanh::lean_is_exclusive(v___x_4932_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4935_ = v___x_4932_;
                        v_isShared_4936_ = v_isSharedCheck_4984_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4933_);
                        crate::leanh::lean_dec(v___x_4932_);
                        v___x_4935_ = crate::leanh::lean_box(0);
                        v_isShared_4936_ = v_isSharedCheck_4984_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_4923_);
                    crate::leanh::lean_dec_ref(v_e_4922_);
                    v_a_4985_ = crate::leanh::lean_ctor_get(v___x_4932_, 0);
                    v_isSharedCheck_4992_ = (!crate::leanh::lean_is_exclusive(v___x_4932_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4987_ = v___x_4932_;
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4985_);
                        crate::leanh::lean_dec(v___x_4932_);
                        v___x_4987_ = crate::leanh::lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4933_) == 1 {
                    crate::leanh::lean_del_object(v___x_4935_);
                    crate::leanh::lean_dec_ref(v_type_4923_);
                    v_val_4937_ = crate::leanh::lean_ctor_get(v_a_4933_, 0);
                    crate::leanh::lean_inc(v_val_4937_);
                    crate::leanh::lean_dec_ref_known(v_a_4933_, 1);
                    v___x_4938_ =
                        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(
                            v_e_4922_,
                            v_val_4937_,
                            v_a_4925_,
                            v_a_4926_,
                            v_a_4927_,
                            v_a_4928_,
                            v_a_4929_,
                            v_a_4930_,
                        );
                    return v___x_4938_;
                } else {
                    crate::leanh::lean_dec(v_a_4933_);
                    if v_report_4924_ == 0 {
                        crate::leanh::lean_dec_ref(v_type_4923_);
                        if v_isShared_4936_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4935_, 0, v_e_4922_);
                            v___x_4940_ = v___x_4935_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4941_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_e_4922_);
                            v___x_4940_ = v_reuseFailAlloc_4941_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4935_);
                        v___x_4942_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4925_);
                        if crate::leanh::lean_obj_tag(v___x_4942_) == 0 {
                            v_a_4943_ = crate::leanh::lean_ctor_get(v___x_4942_, 0);
                            v_isSharedCheck_4975_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4942_)) as u8;
                            if v_isSharedCheck_4975_ == 0 {
                                v___x_4945_ = v___x_4942_;
                                v_isShared_4946_ = v_isSharedCheck_4975_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4943_);
                                crate::leanh::lean_dec(v___x_4942_);
                                v___x_4945_ = crate::leanh::lean_box(0);
                                v_isShared_4946_ = v_isSharedCheck_4975_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_type_4923_);
                            crate::leanh::lean_dec_ref(v_e_4922_);
                            v_a_4976_ = crate::leanh::lean_ctor_get(v___x_4942_, 0);
                            v_isSharedCheck_4983_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4942_)) as u8;
                            if v_isSharedCheck_4983_ == 0 {
                                v___x_4978_ = v___x_4942_;
                                v_isShared_4979_ = v_isSharedCheck_4983_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4976_);
                                crate::leanh::lean_dec(v___x_4942_);
                                v___x_4978_ = crate::leanh::lean_box(0);
                                v_isShared_4979_ = v_isSharedCheck_4983_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4940_;
            }
            3 => {
                v___x_4947_ = (crate::leanh::lean_unbox(v_a_4943_) as u8);
                crate::leanh::lean_dec(v_a_4943_);
                if v___x_4947_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_4923_);
                    if v_isShared_4946_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4945_, 0, v_e_4922_);
                        v___x_4949_ = v___x_4945_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_e_4922_);
                        v___x_4949_ = v_reuseFailAlloc_4950_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4945_);
                    v___x_4951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst___closed__1);
                    crate::leanh::lean_inc_ref(v_e_4922_);
                    v___x_4952_ = l_Lean_indentExpr(v_e_4922_);
                    v___x_4953_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4953_, 0, v___x_4951_);
                    crate::leanh::lean_ctor_set(v___x_4953_, 1, v___x_4952_);
                    v___x_4954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___closed__1);
                    v___x_4955_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4955_, 0, v___x_4953_);
                    crate::leanh::lean_ctor_set(v___x_4955_, 1, v___x_4954_);
                    v___x_4956_ = l_Lean_indentExpr(v_type_4923_);
                    v___x_4957_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4957_, 0, v___x_4955_);
                    crate::leanh::lean_ctor_set(v___x_4957_, 1, v___x_4956_);
                    v___x_4958_ = l_Lean_Meta_Sym_reportIssue(
                        v___x_4957_,
                        v_a_4925_,
                        v_a_4926_,
                        v_a_4927_,
                        v_a_4928_,
                        v_a_4929_,
                        v_a_4930_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4958_) == 0 {
                        v_isSharedCheck_4965_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4958_)) as u8;
                        if v_isSharedCheck_4965_ == 0 {
                            v_unused_4966_ = crate::leanh::lean_ctor_get(v___x_4958_, 0);
                            crate::leanh::lean_dec(v_unused_4966_);
                            v___x_4960_ = v___x_4958_;
                            v_isShared_4961_ = v_isSharedCheck_4965_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4958_);
                            v___x_4960_ = crate::leanh::lean_box(0);
                            v_isShared_4961_ = v_isSharedCheck_4965_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4922_);
                        v_a_4967_ = crate::leanh::lean_ctor_get(v___x_4958_, 0);
                        v_isSharedCheck_4974_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4958_)) as u8;
                        if v_isSharedCheck_4974_ == 0 {
                            v___x_4969_ = v___x_4958_;
                            v_isShared_4970_ = v_isSharedCheck_4974_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4967_);
                            crate::leanh::lean_dec(v___x_4958_);
                            v___x_4969_ = crate::leanh::lean_box(0);
                            v_isShared_4970_ = v_isSharedCheck_4974_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_4949_;
            }
            5 => {
                if v_isShared_4961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4960_, 0, v_e_4922_);
                    v___x_4963_ = v___x_4960_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_e_4922_);
                    v___x_4963_ = v_reuseFailAlloc_4964_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4963_;
            }
            7 => {
                if v_isShared_4970_ == 0 {
                    v___x_4972_ = v___x_4969_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
                    v___x_4972_ = v_reuseFailAlloc_4973_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4972_;
            }
            9 => {
                if v_isShared_4979_ == 0 {
                    v___x_4981_ = v___x_4978_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
                    v___x_4981_ = v_reuseFailAlloc_4982_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4981_;
            }
            11 => {
                if v_isShared_4988_ == 0 {
                    v___x_4990_ = v___x_4987_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
                    v___x_4990_ = v_reuseFailAlloc_4991_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg___boxed(
    mut v_e_4993_: *mut crate::leanh::LeanObject,
    mut v_type_4994_: *mut crate::leanh::LeanObject,
    mut v_report_4995_: *mut crate::leanh::LeanObject,
    mut v_a_4996_: *mut crate::leanh::LeanObject,
    mut v_a_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
    mut v_a_5000_: *mut crate::leanh::LeanObject,
    mut v_a_5001_: *mut crate::leanh::LeanObject,
    mut v_a_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_report_boxed_5003_: u8 = 0;
    let mut v_res_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_report_boxed_5003_ = (crate::leanh::lean_unbox(v_report_4995_) as u8);
    v_res_5004_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(
            v_e_4993_,
            v_type_4994_,
            v_report_boxed_5003_,
            v_a_4996_,
            v_a_4997_,
            v_a_4998_,
            v_a_4999_,
            v_a_5000_,
            v_a_5001_,
        );
    crate::leanh::lean_dec(v_a_5001_);
    crate::leanh::lean_dec_ref(v_a_5000_);
    crate::leanh::lean_dec(v_a_4999_);
    crate::leanh::lean_dec_ref(v_a_4998_);
    crate::leanh::lean_dec(v_a_4997_);
    crate::leanh::lean_dec_ref(v_a_4996_);
    return v_res_5004_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(
    mut v_e_5005_: *mut crate::leanh::LeanObject,
    mut v_type_5006_: *mut crate::leanh::LeanObject,
    mut v_report_5007_: u8,
    mut v_a_5008_: u8,
    mut v_a_5009_: *mut crate::leanh::LeanObject,
    mut v_a_5010_: *mut crate::leanh::LeanObject,
    mut v_a_5011_: *mut crate::leanh::LeanObject,
    mut v_a_5012_: *mut crate::leanh::LeanObject,
    mut v_a_5013_: *mut crate::leanh::LeanObject,
    mut v_a_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5016_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(
            v_e_5005_,
            v_type_5006_,
            v_report_5007_,
            v_a_5009_,
            v_a_5010_,
            v_a_5011_,
            v_a_5012_,
            v_a_5013_,
            v_a_5014_,
        );
    return v___x_5016_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___boxed(
    mut v_e_5017_: *mut crate::leanh::LeanObject,
    mut v_type_5018_: *mut crate::leanh::LeanObject,
    mut v_report_5019_: *mut crate::leanh::LeanObject,
    mut v_a_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
    mut v_a_5025_: *mut crate::leanh::LeanObject,
    mut v_a_5026_: *mut crate::leanh::LeanObject,
    mut v_a_5027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_report_boxed_5028_: u8 = 0;
    let mut v_a_boxed_5029_: u8 = 0;
    let mut v_res_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_report_boxed_5028_ = (crate::leanh::lean_unbox(v_report_5019_) as u8);
    v_a_boxed_5029_ = (crate::leanh::lean_unbox(v_a_5020_) as u8);
    v_res_5030_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore(
        v_e_5017_,
        v_type_5018_,
        v_report_boxed_5028_,
        v_a_boxed_5029_,
        v_a_5021_,
        v_a_5022_,
        v_a_5023_,
        v_a_5024_,
        v_a_5025_,
        v_a_5026_,
    );
    crate::leanh::lean_dec(v_a_5026_);
    crate::leanh::lean_dec_ref(v_a_5025_);
    crate::leanh::lean_dec(v_a_5024_);
    crate::leanh::lean_dec_ref(v_a_5023_);
    crate::leanh::lean_dec(v_a_5022_);
    crate::leanh::lean_dec_ref(v_a_5021_);
    return v_res_5030_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_x_5032_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5033_: u8 = 0;
    let mut v_key_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5032_) == 0 {
                    v___x_5033_ = 0;
                    return v___x_5033_;
                } else {
                    v_key_5034_ = crate::leanh::lean_ctor_get(v_x_5032_, 0);
                    v_tail_5035_ = crate::leanh::lean_ctor_get(v_x_5032_, 2);
                    v___x_5036_ = lean_expr_eqv(v_key_5034_, v_a_5031_);
                    if v___x_5036_ == 0 {
                        v_x_5032_ = v_tail_5035_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5036_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg___boxed(
    mut v_a_5038_: *mut crate::leanh::LeanObject,
    mut v_x_5039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5040_: u8 = 0;
    let mut v_r_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_5038_, v_x_5039_);
    crate::leanh::lean_dec(v_x_5039_);
    crate::leanh::lean_dec_ref(v_a_5038_);
    v_r_5041_ = crate::leanh::lean_box((v_res_5040_) as usize);
    return v_r_5041_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(
    mut v_x_5042_: *mut crate::leanh::LeanObject,
    mut v_x_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u64 = 0;
    let mut v___x_5052_: u64 = 0;
    let mut v___x_5053_: u64 = 0;
    let mut v_fold_5054_: u64 = 0;
    let mut v___x_5055_: u64 = 0;
    let mut v___x_5056_: u64 = 0;
    let mut v___x_5057_: u64 = 0;
    let mut v___x_5058_: usize = 0;
    let mut v___x_5059_: usize = 0;
    let mut v___x_5060_: usize = 0;
    let mut v___x_5061_: usize = 0;
    let mut v___x_5062_: usize = 0;
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5043_) == 0 {
                    return v_x_5042_;
                } else {
                    v_key_5044_ = crate::leanh::lean_ctor_get(v_x_5043_, 0);
                    v_value_5045_ = crate::leanh::lean_ctor_get(v_x_5043_, 1);
                    v_tail_5046_ = crate::leanh::lean_ctor_get(v_x_5043_, 2);
                    v_isSharedCheck_5069_ = (!crate::leanh::lean_is_exclusive(v_x_5043_)) as u8;
                    if v_isSharedCheck_5069_ == 0 {
                        v___x_5048_ = v_x_5043_;
                        v_isShared_5049_ = v_isSharedCheck_5069_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5046_);
                        crate::leanh::lean_inc(v_value_5045_);
                        crate::leanh::lean_inc(v_key_5044_);
                        crate::leanh::lean_dec(v_x_5043_);
                        v___x_5048_ = crate::leanh::lean_box(0);
                        v_isShared_5049_ = v_isSharedCheck_5069_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5050_ = lean_array_get_size(v_x_5042_);
                v___x_5051_ = l_Lean_Expr_hash(v_key_5044_);
                v___x_5052_ = 32u64;
                v___x_5053_ = lean_uint64_shift_right(v___x_5051_, v___x_5052_);
                v_fold_5054_ = lean_uint64_xor(v___x_5051_, v___x_5053_);
                v___x_5055_ = 16u64;
                v___x_5056_ = lean_uint64_shift_right(v_fold_5054_, v___x_5055_);
                v___x_5057_ = lean_uint64_xor(v_fold_5054_, v___x_5056_);
                v___x_5058_ = lean_uint64_to_usize(v___x_5057_);
                v___x_5059_ = lean_usize_of_nat(v___x_5050_);
                v___x_5060_ = 1usize;
                v___x_5061_ = lean_usize_sub(v___x_5059_, v___x_5060_);
                v___x_5062_ = lean_usize_land(v___x_5058_, v___x_5061_);
                v___x_5063_ = lean_array_uget_borrowed(v_x_5042_, v___x_5062_);
                crate::leanh::lean_inc(v___x_5063_);
                if v_isShared_5049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5048_, 2, v___x_5063_);
                    v___x_5065_ = v___x_5048_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_key_5044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 1, v_value_5045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 2, v___x_5063_);
                    v___x_5065_ = v_reuseFailAlloc_5068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5066_ = lean_array_uset(v_x_5042_, v___x_5062_, v___x_5065_);
                v_x_5042_ = v___x_5066_;
                v_x_5043_ = v_tail_5046_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(
    mut v_i_5070_: *mut crate::leanh::LeanObject,
    mut v_source_5071_: *mut crate::leanh::LeanObject,
    mut v_target_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: u8 = 0;
    let mut v_es_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5073_ = lean_array_get_size(v_source_5071_);
                v___x_5074_ = lean_nat_dec_lt(v_i_5070_, v___x_5073_);
                if v___x_5074_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5071_);
                    crate::leanh::lean_dec(v_i_5070_);
                    return v_target_5072_;
                } else {
                    v_es_5075_ = lean_array_fget(v_source_5071_, v_i_5070_);
                    v___x_5076_ = crate::leanh::lean_box(0);
                    v_source_5077_ = lean_array_fset(v_source_5071_, v_i_5070_, v___x_5076_);
                    v_target_5078_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_target_5072_, v_es_5075_);
                    v___x_5079_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5080_ = lean_nat_add(v_i_5070_, v___x_5079_);
                    crate::leanh::lean_dec(v_i_5070_);
                    v_i_5070_ = v___x_5080_;
                    v_source_5071_ = v_source_5077_;
                    v_target_5072_ = v_target_5078_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(
    mut v_data_5082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5083_ = lean_array_get_size(v_data_5082_);
    v___x_5084_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5085_ = lean_nat_mul(v___x_5083_, v___x_5084_);
    v___x_5086_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5087_ = crate::leanh::lean_box(0);
    v___x_5088_ = lean_mk_array(v_nbuckets_5085_, v___x_5087_);
    v___x_5089_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v___x_5086_, v_data_5082_, v___x_5088_);
    return v___x_5089_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(
    mut v_a_5090_: *mut crate::leanh::LeanObject,
    mut v_b_5091_: *mut crate::leanh::LeanObject,
    mut v_x_5092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5092_) == 0 {
                    crate::leanh::lean_dec(v_b_5091_);
                    crate::leanh::lean_dec_ref(v_a_5090_);
                    return v_x_5092_;
                } else {
                    v_key_5093_ = crate::leanh::lean_ctor_get(v_x_5092_, 0);
                    v_value_5094_ = crate::leanh::lean_ctor_get(v_x_5092_, 1);
                    v_tail_5095_ = crate::leanh::lean_ctor_get(v_x_5092_, 2);
                    v_isSharedCheck_5107_ = (!crate::leanh::lean_is_exclusive(v_x_5092_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5097_ = v_x_5092_;
                        v_isShared_5098_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5095_);
                        crate::leanh::lean_inc(v_value_5094_);
                        crate::leanh::lean_inc(v_key_5093_);
                        crate::leanh::lean_dec(v_x_5092_);
                        v___x_5097_ = crate::leanh::lean_box(0);
                        v_isShared_5098_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5099_ = lean_expr_eqv(v_key_5093_, v_a_5090_);
                if v___x_5099_ == 0 {
                    v___x_5100_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_5090_, v_b_5091_, v_tail_5095_);
                    if v_isShared_5098_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5097_, 2, v___x_5100_);
                        v___x_5102_ = v___x_5097_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5103_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_key_5093_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_value_5094_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 2, v___x_5100_);
                        v___x_5102_ = v_reuseFailAlloc_5103_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_5094_);
                    crate::leanh::lean_dec(v_key_5093_);
                    if v_isShared_5098_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5097_, 1, v_b_5091_);
                        crate::leanh::lean_ctor_set(v___x_5097_, 0, v_a_5090_);
                        v___x_5105_ = v___x_5097_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5106_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5090_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 1, v_b_5091_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 2, v_tail_5095_);
                        v___x_5105_ = v_reuseFailAlloc_5106_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5102_;
            }
            3 => {
                return v___x_5105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(
    mut v_m_5108_: *mut crate::leanh::LeanObject,
    mut v_a_5109_: *mut crate::leanh::LeanObject,
    mut v_b_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u64 = 0;
    let mut v___x_5118_: u64 = 0;
    let mut v___x_5119_: u64 = 0;
    let mut v_fold_5120_: u64 = 0;
    let mut v___x_5121_: u64 = 0;
    let mut v___x_5122_: u64 = 0;
    let mut v___x_5123_: u64 = 0;
    let mut v___x_5124_: usize = 0;
    let mut v___x_5125_: usize = 0;
    let mut v___x_5126_: usize = 0;
    let mut v___x_5127_: usize = 0;
    let mut v___x_5128_: usize = 0;
    let mut v_bkt_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: u8 = 0;
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: u8 = 0;
    let mut v_val_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5111_ = crate::leanh::lean_ctor_get(v_m_5108_, 0);
                v_buckets_5112_ = crate::leanh::lean_ctor_get(v_m_5108_, 1);
                v_isSharedCheck_5155_ = (!crate::leanh::lean_is_exclusive(v_m_5108_)) as u8;
                if v_isSharedCheck_5155_ == 0 {
                    v___x_5114_ = v_m_5108_;
                    v_isShared_5115_ = v_isSharedCheck_5155_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5112_);
                    crate::leanh::lean_inc(v_size_5111_);
                    crate::leanh::lean_dec(v_m_5108_);
                    v___x_5114_ = crate::leanh::lean_box(0);
                    v_isShared_5115_ = v_isSharedCheck_5155_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5116_ = lean_array_get_size(v_buckets_5112_);
                v___x_5117_ = l_Lean_Expr_hash(v_a_5109_);
                v___x_5118_ = 32u64;
                v___x_5119_ = lean_uint64_shift_right(v___x_5117_, v___x_5118_);
                v_fold_5120_ = lean_uint64_xor(v___x_5117_, v___x_5119_);
                v___x_5121_ = 16u64;
                v___x_5122_ = lean_uint64_shift_right(v_fold_5120_, v___x_5121_);
                v___x_5123_ = lean_uint64_xor(v_fold_5120_, v___x_5122_);
                v___x_5124_ = lean_uint64_to_usize(v___x_5123_);
                v___x_5125_ = lean_usize_of_nat(v___x_5116_);
                v___x_5126_ = 1usize;
                v___x_5127_ = lean_usize_sub(v___x_5125_, v___x_5126_);
                v___x_5128_ = lean_usize_land(v___x_5124_, v___x_5127_);
                v_bkt_5129_ = lean_array_uget_borrowed(v_buckets_5112_, v___x_5128_);
                v___x_5130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_5109_, v_bkt_5129_);
                if v___x_5130_ == 0 {
                    v___x_5131_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5132_ = lean_nat_add(v_size_5111_, v___x_5131_);
                    crate::leanh::lean_dec(v_size_5111_);
                    crate::leanh::lean_inc(v_bkt_5129_);
                    v___x_5133_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5133_, 0, v_a_5109_);
                    crate::leanh::lean_ctor_set(v___x_5133_, 1, v_b_5110_);
                    crate::leanh::lean_ctor_set(v___x_5133_, 2, v_bkt_5129_);
                    v_buckets_x27_5134_ =
                        lean_array_uset(v_buckets_5112_, v___x_5128_, v___x_5133_);
                    v___x_5135_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5136_ = lean_nat_mul(v_size_x27_5132_, v___x_5135_);
                    v___x_5137_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5138_ = lean_nat_div(v___x_5136_, v___x_5137_);
                    crate::leanh::lean_dec(v___x_5136_);
                    v___x_5139_ = lean_array_get_size(v_buckets_x27_5134_);
                    v___x_5140_ = lean_nat_dec_le(v___x_5138_, v___x_5139_);
                    crate::leanh::lean_dec(v___x_5138_);
                    if v___x_5140_ == 0 {
                        v_val_5141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_buckets_x27_5134_);
                        if v_isShared_5115_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5114_, 1, v_val_5141_);
                            crate::leanh::lean_ctor_set(v___x_5114_, 0, v_size_x27_5132_);
                            v___x_5143_ = v___x_5114_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5144_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5144_,
                                0,
                                v_size_x27_5132_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_val_5141_);
                            v___x_5143_ = v_reuseFailAlloc_5144_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5115_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5114_, 1, v_buckets_x27_5134_);
                            crate::leanh::lean_ctor_set(v___x_5114_, 0, v_size_x27_5132_);
                            v___x_5146_ = v___x_5114_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5147_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5147_,
                                0,
                                v_size_x27_5132_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5147_,
                                1,
                                v_buckets_x27_5134_,
                            );
                            v___x_5146_ = v_reuseFailAlloc_5147_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_5129_);
                    v___x_5148_ = crate::leanh::lean_box(0);
                    v_buckets_x27_5149_ =
                        lean_array_uset(v_buckets_5112_, v___x_5128_, v___x_5148_);
                    v___x_5150_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_5109_, v_b_5110_, v_bkt_5129_);
                    v___x_5151_ = lean_array_uset(v_buckets_x27_5149_, v___x_5128_, v___x_5150_);
                    if v_isShared_5115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5114_, 1, v___x_5151_);
                        v___x_5153_ = v___x_5114_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_size_5111_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 1, v___x_5151_);
                        v___x_5153_ = v_reuseFailAlloc_5154_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5143_;
            }
            3 => {
                return v___x_5146_;
            }
            4 => {
                return v___x_5153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(
    mut v_k_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: u8,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v_b_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5166_ = crate::leanh::lean_box((v___y_5157_) as usize);
    crate::leanh::lean_inc(v___y_5164_);
    crate::leanh::lean_inc_ref(v___y_5163_);
    crate::leanh::lean_inc(v___y_5162_);
    crate::leanh::lean_inc_ref(v___y_5161_);
    crate::leanh::lean_inc(v___y_5159_);
    crate::leanh::lean_inc_ref(v___y_5158_);
    v___x_5167_ = crate::leanh::lean_apply_9(
        v_k_5156_,
        v_b_5160_,
        v___x_5166_,
        v___y_5158_,
        v___y_5159_,
        v___y_5161_,
        v___y_5162_,
        v___y_5163_,
        v___y_5164_,
        crate::leanh::lean_box(0),
    );
    return v___x_5167_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed(
    mut v_k_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v_b_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_63904__boxed_5178_: u8 = 0;
    let mut v_res_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_63904__boxed_5178_ = (crate::leanh::lean_unbox(v___y_5169_) as u8);
    v_res_5179_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0(v_k_5168_, v___y_63904__boxed_5178_, v___y_5170_, v___y_5171_, v_b_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
    crate::leanh::lean_dec(v___y_5176_);
    crate::leanh::lean_dec_ref(v___y_5175_);
    crate::leanh::lean_dec(v___y_5174_);
    crate::leanh::lean_dec_ref(v___y_5173_);
    crate::leanh::lean_dec(v___y_5171_);
    crate::leanh::lean_dec_ref(v___y_5170_);
    return v_res_5179_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(
    mut v_name_5180_: *mut crate::leanh::LeanObject,
    mut v_bi_5181_: u8,
    mut v_type_5182_: *mut crate::leanh::LeanObject,
    mut v_k_5183_: *mut crate::leanh::LeanObject,
    mut v_kind_5184_: u8,
    mut v___y_5185_: u8,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
    mut v___y_5190_: *mut crate::leanh::LeanObject,
    mut v___y_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5199_: u8 = 0;
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5193_ = crate::leanh::lean_box((v___y_5185_) as usize);
                crate::leanh::lean_inc(v___y_5187_);
                crate::leanh::lean_inc_ref(v___y_5186_);
                v___f_5194_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                crate::leanh::lean_closure_set(v___f_5194_, 0, v_k_5183_);
                crate::leanh::lean_closure_set(v___f_5194_, 1, v___x_5193_);
                crate::leanh::lean_closure_set(v___f_5194_, 2, v___y_5186_);
                crate::leanh::lean_closure_set(v___f_5194_, 3, v___y_5187_);
                v___x_5195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_5180_,
                    v_bi_5181_,
                    v_type_5182_,
                    v___f_5194_,
                    v_kind_5184_,
                    v___y_5188_,
                    v___y_5189_,
                    v___y_5190_,
                    v___y_5191_,
                );
                if crate::leanh::lean_obj_tag(v___x_5195_) == 0 {
                    return v___x_5195_;
                } else {
                    v_a_5196_ = crate::leanh::lean_ctor_get(v___x_5195_, 0);
                    v_isSharedCheck_5203_ = (!crate::leanh::lean_is_exclusive(v___x_5195_)) as u8;
                    if v_isSharedCheck_5203_ == 0 {
                        v___x_5198_ = v___x_5195_;
                        v_isShared_5199_ = v_isSharedCheck_5203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5196_);
                        crate::leanh::lean_dec(v___x_5195_);
                        v___x_5198_ = crate::leanh::lean_box(0);
                        v_isShared_5199_ = v_isSharedCheck_5203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5199_ == 0 {
                    v___x_5201_ = v___x_5198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
                    v___x_5201_ = v_reuseFailAlloc_5202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg___boxed(
    mut v_name_5204_: *mut crate::leanh::LeanObject,
    mut v_bi_5205_: *mut crate::leanh::LeanObject,
    mut v_type_5206_: *mut crate::leanh::LeanObject,
    mut v_k_5207_: *mut crate::leanh::LeanObject,
    mut v_kind_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_5217_: u8 = 0;
    let mut v_kind_boxed_5218_: u8 = 0;
    let mut v___y_63932__boxed_5219_: u8 = 0;
    let mut v_res_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_5217_ = (crate::leanh::lean_unbox(v_bi_5205_) as u8);
    v_kind_boxed_5218_ = (crate::leanh::lean_unbox(v_kind_5208_) as u8);
    v___y_63932__boxed_5219_ = (crate::leanh::lean_unbox(v___y_5209_) as u8);
    v_res_5220_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_5204_, v_bi_boxed_5217_, v_type_5206_, v_k_5207_, v_kind_boxed_5218_, v___y_63932__boxed_5219_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
    crate::leanh::lean_dec(v___y_5215_);
    crate::leanh::lean_dec_ref(v___y_5214_);
    crate::leanh::lean_dec(v___y_5213_);
    crate::leanh::lean_dec_ref(v___y_5212_);
    crate::leanh::lean_dec(v___y_5211_);
    crate::leanh::lean_dec_ref(v___y_5210_);
    return v_res_5220_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(
    mut v_declName_5221_: *mut crate::leanh::LeanObject,
    mut v___y_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: u8 = 0;
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5224_ = lean_st_ref_get(v___y_5222_);
    v_env_5225_ = crate::leanh::lean_ctor_get(v___x_5224_, 0);
    crate::leanh::lean_inc_ref(v_env_5225_);
    crate::leanh::lean_dec(v___x_5224_);
    v___x_5226_ = lean_is_matcher(v_env_5225_, v_declName_5221_);
    v___x_5227_ = crate::leanh::lean_box((v___x_5226_) as usize);
    v___x_5228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5228_, 0, v___x_5227_);
    return v___x_5228_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg___boxed(
    mut v_declName_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5232_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_5229_, v___y_5230_);
    crate::leanh::lean_dec(v___y_5230_);
    return v_res_5232_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(
    mut v_msgData_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5239_ = lean_st_ref_get(v___y_5237_);
    v_env_5240_ = crate::leanh::lean_ctor_get(v___x_5239_, 0);
    crate::leanh::lean_inc_ref(v_env_5240_);
    crate::leanh::lean_dec(v___x_5239_);
    v___x_5241_ = lean_st_ref_get(v___y_5235_);
    v_mctx_5242_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5242_);
    crate::leanh::lean_dec(v___x_5241_);
    v_lctx_5243_ = crate::leanh::lean_ctor_get(v___y_5234_, 2);
    v_options_5244_ = crate::leanh::lean_ctor_get(v___y_5236_, 2);
    crate::leanh::lean_inc_ref(v_options_5244_);
    crate::leanh::lean_inc_ref(v_lctx_5243_);
    v___x_5245_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5245_, 0, v_env_5240_);
    crate::leanh::lean_ctor_set(v___x_5245_, 1, v_mctx_5242_);
    crate::leanh::lean_ctor_set(v___x_5245_, 2, v_lctx_5243_);
    crate::leanh::lean_ctor_set(v___x_5245_, 3, v_options_5244_);
    v___x_5246_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5246_, 0, v___x_5245_);
    crate::leanh::lean_ctor_set(v___x_5246_, 1, v_msgData_5233_);
    v___x_5247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5247_, 0, v___x_5246_);
    return v___x_5247_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21___boxed(
    mut v_msgData_5248_: *mut crate::leanh::LeanObject,
    mut v___y_5249_: *mut crate::leanh::LeanObject,
    mut v___y_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5254_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msgData_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_);
    crate::leanh::lean_dec(v___y_5252_);
    crate::leanh::lean_dec_ref(v___y_5251_);
    crate::leanh::lean_dec(v___y_5250_);
    crate::leanh::lean_dec_ref(v___y_5249_);
    return v_res_5254_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0()
-> f64 {
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: f64 = 0.0;
    v___x_5255_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5256_ = lean_float_of_nat(v___x_5255_);
    return v___x_5256_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(
    mut v_cls_5260_: *mut crate::leanh::LeanObject,
    mut v_msg_5261_: *mut crate::leanh::LeanObject,
    mut v___y_5262_: *mut crate::leanh::LeanObject,
    mut v___y_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5272_: u8 = 0;
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5285_: u8 = 0;
    let mut v_tid_5286_: u64 = 0;
    let mut v_traces_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: f64 = 0.0;
    let mut v___x_5293_: u8 = 0;
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5311_: u8 = 0;
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut v_isSharedCheck_5313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5267_ = crate::leanh::lean_ctor_get(v___y_5264_, 5);
                v___x_5268_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9_spec__21(v_msg_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
                v_a_5269_ = crate::leanh::lean_ctor_get(v___x_5268_, 0);
                v_isSharedCheck_5313_ = (!crate::leanh::lean_is_exclusive(v___x_5268_)) as u8;
                if v_isSharedCheck_5313_ == 0 {
                    v___x_5271_ = v___x_5268_;
                    v_isShared_5272_ = v_isSharedCheck_5313_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5269_);
                    crate::leanh::lean_dec(v___x_5268_);
                    v___x_5271_ = crate::leanh::lean_box(0);
                    v_isShared_5272_ = v_isSharedCheck_5313_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5273_ = lean_st_ref_take(v___y_5265_);
                v_traceState_5274_ = crate::leanh::lean_ctor_get(v___x_5273_, 4);
                v_env_5275_ = crate::leanh::lean_ctor_get(v___x_5273_, 0);
                v_nextMacroScope_5276_ = crate::leanh::lean_ctor_get(v___x_5273_, 1);
                v_ngen_5277_ = crate::leanh::lean_ctor_get(v___x_5273_, 2);
                v_auxDeclNGen_5278_ = crate::leanh::lean_ctor_get(v___x_5273_, 3);
                v_cache_5279_ = crate::leanh::lean_ctor_get(v___x_5273_, 5);
                v_messages_5280_ = crate::leanh::lean_ctor_get(v___x_5273_, 6);
                v_infoState_5281_ = crate::leanh::lean_ctor_get(v___x_5273_, 7);
                v_snapshotTasks_5282_ = crate::leanh::lean_ctor_get(v___x_5273_, 8);
                v_isSharedCheck_5312_ = (!crate::leanh::lean_is_exclusive(v___x_5273_)) as u8;
                if v_isSharedCheck_5312_ == 0 {
                    v___x_5284_ = v___x_5273_;
                    v_isShared_5285_ = v_isSharedCheck_5312_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5282_);
                    crate::leanh::lean_inc(v_infoState_5281_);
                    crate::leanh::lean_inc(v_messages_5280_);
                    crate::leanh::lean_inc(v_cache_5279_);
                    crate::leanh::lean_inc(v_traceState_5274_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5278_);
                    crate::leanh::lean_inc(v_ngen_5277_);
                    crate::leanh::lean_inc(v_nextMacroScope_5276_);
                    crate::leanh::lean_inc(v_env_5275_);
                    crate::leanh::lean_dec(v___x_5273_);
                    v___x_5284_ = crate::leanh::lean_box(0);
                    v_isShared_5285_ = v_isSharedCheck_5312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5286_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5274_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5287_ = crate::leanh::lean_ctor_get(v_traceState_5274_, 0);
                v_isSharedCheck_5311_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5274_)) as u8;
                if v_isSharedCheck_5311_ == 0 {
                    v___x_5289_ = v_traceState_5274_;
                    v_isShared_5290_ = v_isSharedCheck_5311_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5287_);
                    crate::leanh::lean_dec(v_traceState_5274_);
                    v___x_5289_ = crate::leanh::lean_box(0);
                    v_isShared_5290_ = v_isSharedCheck_5311_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5291_ = crate::leanh::lean_box(0);
                v___x_5292_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__0);
                v___x_5293_ = 0;
                v___x_5294_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__1;
                v___x_5295_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5295_, 0, v_cls_5260_);
                crate::leanh::lean_ctor_set(v___x_5295_, 1, v___x_5291_);
                crate::leanh::lean_ctor_set(v___x_5295_, 2, v___x_5294_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5295_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5292_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5295_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5292_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5295_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5293_,
                );
                v___x_5296_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___closed__2;
                v___x_5297_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5297_, 0, v___x_5295_);
                crate::leanh::lean_ctor_set(v___x_5297_, 1, v_a_5269_);
                crate::leanh::lean_ctor_set(v___x_5297_, 2, v___x_5296_);
                crate::leanh::lean_inc(v_ref_5267_);
                v___x_5298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5298_, 0, v_ref_5267_);
                crate::leanh::lean_ctor_set(v___x_5298_, 1, v___x_5297_);
                v___x_5299_ = l_Lean_PersistentArray_push___redArg(v_traces_5287_, v___x_5298_);
                if v_isShared_5290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5289_, 0, v___x_5299_);
                    v___x_5301_ = v___x_5289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5310_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5299_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5310_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5286_,
                    );
                    v___x_5301_ = v_reuseFailAlloc_5310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5284_, 4, v___x_5301_);
                    v___x_5303_ = v___x_5284_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_env_5275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 1, v_nextMacroScope_5276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 2, v_ngen_5277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 3, v_auxDeclNGen_5278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 4, v___x_5301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 5, v_cache_5279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 6, v_messages_5280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 7, v_infoState_5281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5309_, 8, v_snapshotTasks_5282_);
                    v___x_5303_ = v_reuseFailAlloc_5309_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5304_ = lean_st_ref_set(v___y_5265_, v___x_5303_);
                v___x_5305_ = crate::leanh::lean_box(0);
                if v_isShared_5272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5271_, 0, v___x_5305_);
                    v___x_5307_ = v___x_5271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5308_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5308_, 0, v___x_5305_);
                    v___x_5307_ = v_reuseFailAlloc_5308_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg___boxed(
    mut v_cls_5314_: *mut crate::leanh::LeanObject,
    mut v_msg_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
    mut v___y_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
    mut v___y_5320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5321_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_5314_, v_msg_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
    crate::leanh::lean_dec(v___y_5319_);
    crate::leanh::lean_dec_ref(v___y_5318_);
    crate::leanh::lean_dec(v___y_5317_);
    crate::leanh::lean_dec_ref(v___y_5316_);
    return v_res_5321_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(
    mut v_a_5322_: *mut crate::leanh::LeanObject,
    mut v_x_5323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: u8 = 0;
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5323_) == 0 {
                    v___x_5324_ = crate::leanh::lean_box(0);
                    return v___x_5324_;
                } else {
                    v_key_5325_ = crate::leanh::lean_ctor_get(v_x_5323_, 0);
                    v_value_5326_ = crate::leanh::lean_ctor_get(v_x_5323_, 1);
                    v_tail_5327_ = crate::leanh::lean_ctor_get(v_x_5323_, 2);
                    v___x_5328_ = lean_expr_eqv(v_key_5325_, v_a_5322_);
                    if v___x_5328_ == 0 {
                        v_x_5323_ = v_tail_5327_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5326_);
                        v___x_5330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5330_, 0, v_value_5326_);
                        return v___x_5330_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg___boxed(
    mut v_a_5331_: *mut crate::leanh::LeanObject,
    mut v_x_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5333_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_5331_, v_x_5332_);
    crate::leanh::lean_dec(v_x_5332_);
    crate::leanh::lean_dec_ref(v_a_5331_);
    return v_res_5333_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(
    mut v_m_5334_: *mut crate::leanh::LeanObject,
    mut v_a_5335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u64 = 0;
    let mut v___x_5339_: u64 = 0;
    let mut v___x_5340_: u64 = 0;
    let mut v_fold_5341_: u64 = 0;
    let mut v___x_5342_: u64 = 0;
    let mut v___x_5343_: u64 = 0;
    let mut v___x_5344_: u64 = 0;
    let mut v___x_5345_: usize = 0;
    let mut v___x_5346_: usize = 0;
    let mut v___x_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: usize = 0;
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5336_ = crate::leanh::lean_ctor_get(v_m_5334_, 1);
    v___x_5337_ = lean_array_get_size(v_buckets_5336_);
    v___x_5338_ = l_Lean_Expr_hash(v_a_5335_);
    v___x_5339_ = 32u64;
    v___x_5340_ = lean_uint64_shift_right(v___x_5338_, v___x_5339_);
    v_fold_5341_ = lean_uint64_xor(v___x_5338_, v___x_5340_);
    v___x_5342_ = 16u64;
    v___x_5343_ = lean_uint64_shift_right(v_fold_5341_, v___x_5342_);
    v___x_5344_ = lean_uint64_xor(v_fold_5341_, v___x_5343_);
    v___x_5345_ = lean_uint64_to_usize(v___x_5344_);
    v___x_5346_ = lean_usize_of_nat(v___x_5337_);
    v___x_5347_ = 1usize;
    v___x_5348_ = lean_usize_sub(v___x_5346_, v___x_5347_);
    v___x_5349_ = lean_usize_land(v___x_5345_, v___x_5348_);
    v___x_5350_ = lean_array_uget_borrowed(v_buckets_5336_, v___x_5349_);
    v___x_5351_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_5335_, v___x_5350_);
    return v___x_5351_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg___boxed(
    mut v_m_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5354_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_5352_, v_a_5353_);
    crate::leanh::lean_dec_ref(v_a_5353_);
    crate::leanh::lean_dec_ref(v_m_5352_);
    return v_res_5354_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(
    mut v_name_5355_: *mut crate::leanh::LeanObject,
    mut v_type_5356_: *mut crate::leanh::LeanObject,
    mut v_val_5357_: *mut crate::leanh::LeanObject,
    mut v_k_5358_: *mut crate::leanh::LeanObject,
    mut v_nondep_5359_: u8,
    mut v_kind_5360_: u8,
    mut v___y_5361_: u8,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
    mut v___y_5365_: *mut crate::leanh::LeanObject,
    mut v___y_5366_: *mut crate::leanh::LeanObject,
    mut v___y_5367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5375_: u8 = 0;
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5369_ = crate::leanh::lean_box((v___y_5361_) as usize);
                crate::leanh::lean_inc(v___y_5363_);
                crate::leanh::lean_inc_ref(v___y_5362_);
                v___f_5370_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                crate::leanh::lean_closure_set(v___f_5370_, 0, v_k_5358_);
                crate::leanh::lean_closure_set(v___f_5370_, 1, v___x_5369_);
                crate::leanh::lean_closure_set(v___f_5370_, 2, v___y_5362_);
                crate::leanh::lean_closure_set(v___f_5370_, 3, v___y_5363_);
                v___x_5371_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_5355_,
                    v_type_5356_,
                    v_val_5357_,
                    v___f_5370_,
                    v_nondep_5359_,
                    v_kind_5360_,
                    v___y_5364_,
                    v___y_5365_,
                    v___y_5366_,
                    v___y_5367_,
                );
                if crate::leanh::lean_obj_tag(v___x_5371_) == 0 {
                    return v___x_5371_;
                } else {
                    v_a_5372_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
                    v_isSharedCheck_5379_ = (!crate::leanh::lean_is_exclusive(v___x_5371_)) as u8;
                    if v_isSharedCheck_5379_ == 0 {
                        v___x_5374_ = v___x_5371_;
                        v_isShared_5375_ = v_isSharedCheck_5379_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5372_);
                        crate::leanh::lean_dec(v___x_5371_);
                        v___x_5374_ = crate::leanh::lean_box(0);
                        v_isShared_5375_ = v_isSharedCheck_5379_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5375_ == 0 {
                    v___x_5377_ = v___x_5374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_a_5372_);
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
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg___boxed(
    mut v_name_5380_: *mut crate::leanh::LeanObject,
    mut v_type_5381_: *mut crate::leanh::LeanObject,
    mut v_val_5382_: *mut crate::leanh::LeanObject,
    mut v_k_5383_: *mut crate::leanh::LeanObject,
    mut v_nondep_5384_: *mut crate::leanh::LeanObject,
    mut v_kind_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
    mut v___y_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_5394_: u8 = 0;
    let mut v_kind_boxed_5395_: u8 = 0;
    let mut v___y_64167__boxed_5396_: u8 = 0;
    let mut v_res_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5394_ = (crate::leanh::lean_unbox(v_nondep_5384_) as u8);
    v_kind_boxed_5395_ = (crate::leanh::lean_unbox(v_kind_5385_) as u8);
    v___y_64167__boxed_5396_ = (crate::leanh::lean_unbox(v___y_5386_) as u8);
    v_res_5397_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_5380_, v_type_5381_, v_val_5382_, v_k_5383_, v_nondep_boxed_5394_, v_kind_boxed_5395_, v___y_64167__boxed_5396_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
    crate::leanh::lean_dec(v___y_5392_);
    crate::leanh::lean_dec_ref(v___y_5391_);
    crate::leanh::lean_dec(v___y_5390_);
    crate::leanh::lean_dec_ref(v___y_5389_);
    crate::leanh::lean_dec(v___y_5388_);
    crate::leanh::lean_dec_ref(v___y_5387_);
    return v_res_5397_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(
    mut v_msg_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_Lean_instInhabitedExpr;
    v___x_5400_ = lean_panic_fn_borrowed(v___x_5399_, v_msg_5398_);
    return v___x_5400_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(
    mut v_fvars_5403_: *mut crate::leanh::LeanObject,
    mut v_body_5404_: *mut crate::leanh::LeanObject,
    mut v_x_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: u8,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
    mut v___y_5411_: *mut crate::leanh::LeanObject,
    mut v___y_5412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5414_ = lean_array_push(v_fvars_5403_, v_x_5405_);
    v___x_5415_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(
        v___x_5414_,
        v_body_5404_,
        v___y_5406_,
        v___y_5407_,
        v___y_5408_,
        v___y_5409_,
        v___y_5410_,
        v___y_5411_,
        v___y_5412_,
    );
    return v___x_5415_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed(
    mut v_fvars_5416_: *mut crate::leanh::LeanObject,
    mut v_body_5417_: *mut crate::leanh::LeanObject,
    mut v_x_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_64330__boxed_5427_: u8 = 0;
    let mut v_res_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_64330__boxed_5427_ = (crate::leanh::lean_unbox(v___y_5419_) as u8);
    v_res_5428_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0(
            v_fvars_5416_,
            v_body_5417_,
            v_x_5418_,
            v___y_64330__boxed_5427_,
            v___y_5420_,
            v___y_5421_,
            v___y_5422_,
            v___y_5423_,
            v___y_5424_,
            v___y_5425_,
        );
    crate::leanh::lean_dec(v___y_5425_);
    crate::leanh::lean_dec_ref(v___y_5424_);
    crate::leanh::lean_dec(v___y_5423_);
    crate::leanh::lean_dec_ref(v___y_5422_);
    crate::leanh::lean_dec(v___y_5421_);
    crate::leanh::lean_dec_ref(v___y_5420_);
    return v_res_5428_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(
    mut v_fvars_5429_: *mut crate::leanh::LeanObject,
    mut v_e_5430_: *mut crate::leanh::LeanObject,
    mut v_a_5431_: u8,
    mut v_a_5432_: *mut crate::leanh::LeanObject,
    mut v_a_5433_: *mut crate::leanh::LeanObject,
    mut v_a_5434_: *mut crate::leanh::LeanObject,
    mut v_a_5435_: *mut crate::leanh::LeanObject,
    mut v_a_5436_: *mut crate::leanh::LeanObject,
    mut v_a_5437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_5430_) == 6 {
        let mut v_binderName_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_5442_: u8 = 0;
        let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_5439_ = crate::leanh::lean_ctor_get(v_e_5430_, 0);
        crate::leanh::lean_inc(v_binderName_5439_);
        v_binderType_5440_ = crate::leanh::lean_ctor_get(v_e_5430_, 1);
        crate::leanh::lean_inc_ref(v_binderType_5440_);
        v_body_5441_ = crate::leanh::lean_ctor_get(v_e_5430_, 2);
        crate::leanh::lean_inc_ref(v_body_5441_);
        v_binderInfo_5442_ = crate::leanh::lean_ctor_get_uint8(
            v_e_5430_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_5430_, 3);
        v___x_5443_ = lean_expr_instantiate_rev(v_binderType_5440_, v_fvars_5429_);
        crate::leanh::lean_dec_ref(v_binderType_5440_);
        v___x_5444_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(
            v___x_5443_,
            v_a_5431_,
            v_a_5432_,
            v_a_5433_,
            v_a_5434_,
            v_a_5435_,
            v_a_5436_,
            v_a_5437_,
        );
        if crate::leanh::lean_obj_tag(v___x_5444_) == 0 {
            let mut v_a_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5447_: u8 = 0;
            let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5445_ = crate::leanh::lean_ctor_get(v___x_5444_, 0);
            crate::leanh::lean_inc(v_a_5445_);
            crate::leanh::lean_dec_ref_known(v___x_5444_, 1);
            v___f_5446_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
            crate::leanh::lean_closure_set(v___f_5446_, 0, v_fvars_5429_);
            crate::leanh::lean_closure_set(v___f_5446_, 1, v_body_5441_);
            v___x_5447_ = 0;
            v___x_5448_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_5439_, v_binderInfo_5442_, v_a_5445_, v___f_5446_, v___x_5447_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_);
            return v___x_5448_;
        } else {
            crate::leanh::lean_dec_ref(v_body_5441_);
            crate::leanh::lean_dec(v_binderName_5439_);
            crate::leanh::lean_dec_ref(v_fvars_5429_);
            return v___x_5444_;
        }
    } else {
        let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5449_ = lean_expr_instantiate_rev(v_e_5430_, v_fvars_5429_);
        crate::leanh::lean_dec_ref(v_e_5430_);
        v___x_5450_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
            v___x_5449_,
            v_a_5431_,
            v_a_5432_,
            v_a_5433_,
            v_a_5434_,
            v_a_5435_,
            v_a_5436_,
            v_a_5437_,
        );
        if crate::leanh::lean_obj_tag(v___x_5450_) == 0 {
            let mut v_a_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5452_: u8 = 0;
            let mut v___x_5453_: u8 = 0;
            let mut v___x_5454_: u8 = 0;
            let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5451_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
            crate::leanh::lean_inc(v_a_5451_);
            crate::leanh::lean_dec_ref_known(v___x_5450_, 1);
            v___x_5452_ = 0;
            v___x_5453_ = 1;
            v___x_5454_ = 1;
            v___x_5455_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_5429_,
                v_a_5451_,
                v___x_5452_,
                v___x_5453_,
                v___x_5452_,
                v___x_5453_,
                v___x_5454_,
                v_a_5434_,
                v_a_5435_,
                v_a_5436_,
                v_a_5437_,
            );
            crate::leanh::lean_dec_ref(v_fvars_5429_);
            return v___x_5455_;
        } else {
            crate::leanh::lean_dec_ref(v_fvars_5429_);
            return v___x_5450_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(
    mut v_e_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: u8,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
    mut v_a_5459_: *mut crate::leanh::LeanObject,
    mut v_a_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
    mut v_a_5462_: *mut crate::leanh::LeanObject,
    mut v_a_5463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_a_5457_ == 0 {
        let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5465_ =
            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0;
        v___x_5466_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(
            v___x_5465_,
            v_e_5456_,
            v_a_5457_,
            v_a_5458_,
            v_a_5459_,
            v_a_5460_,
            v_a_5461_,
            v_a_5462_,
            v_a_5463_,
        );
        return v___x_5466_;
    } else {
        let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5467_ =
            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0;
        v___x_5468_ = l_Lean_Meta_Sym_etaReduce(v_e_5456_);
        crate::leanh::lean_dec_ref(v_e_5456_);
        v___x_5469_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(
            v___x_5467_,
            v___x_5468_,
            v_a_5457_,
            v_a_5458_,
            v_a_5459_,
            v_a_5460_,
            v_a_5461_,
            v_a_5462_,
            v_a_5463_,
        );
        return v___x_5469_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(
    mut v_fvars_5470_: *mut crate::leanh::LeanObject,
    mut v_body_5471_: *mut crate::leanh::LeanObject,
    mut v_x_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: u8,
    mut v___y_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5481_ = lean_array_push(v_fvars_5470_, v_x_5472_);
    v___x_5482_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(
        v___x_5481_,
        v_body_5471_,
        v___y_5473_,
        v___y_5474_,
        v___y_5475_,
        v___y_5476_,
        v___y_5477_,
        v___y_5478_,
        v___y_5479_,
    );
    return v___x_5482_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed(
    mut v_fvars_5483_: *mut crate::leanh::LeanObject,
    mut v_body_5484_: *mut crate::leanh::LeanObject,
    mut v_x_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
    mut v___y_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
    mut v___y_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_64341__boxed_5494_: u8 = 0;
    let mut v_res_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_64341__boxed_5494_ = (crate::leanh::lean_unbox(v___y_5486_) as u8);
    v_res_5495_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0(
        v_fvars_5483_,
        v_body_5484_,
        v_x_5485_,
        v___y_64341__boxed_5494_,
        v___y_5487_,
        v___y_5488_,
        v___y_5489_,
        v___y_5490_,
        v___y_5491_,
        v___y_5492_,
    );
    crate::leanh::lean_dec(v___y_5492_);
    crate::leanh::lean_dec_ref(v___y_5491_);
    crate::leanh::lean_dec(v___y_5490_);
    crate::leanh::lean_dec_ref(v___y_5489_);
    crate::leanh::lean_dec(v___y_5488_);
    crate::leanh::lean_dec_ref(v___y_5487_);
    return v_res_5495_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(
    mut v_fvars_5496_: *mut crate::leanh::LeanObject,
    mut v_e_5497_: *mut crate::leanh::LeanObject,
    mut v_a_5498_: u8,
    mut v_a_5499_: *mut crate::leanh::LeanObject,
    mut v_a_5500_: *mut crate::leanh::LeanObject,
    mut v_a_5501_: *mut crate::leanh::LeanObject,
    mut v_a_5502_: *mut crate::leanh::LeanObject,
    mut v_a_5503_: *mut crate::leanh::LeanObject,
    mut v_a_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_5497_) == 8 {
        let mut v_declName_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_5510_: u8 = 0;
        let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_5506_ = crate::leanh::lean_ctor_get(v_e_5497_, 0);
        crate::leanh::lean_inc(v_declName_5506_);
        v_type_5507_ = crate::leanh::lean_ctor_get(v_e_5497_, 1);
        crate::leanh::lean_inc_ref(v_type_5507_);
        v_value_5508_ = crate::leanh::lean_ctor_get(v_e_5497_, 2);
        crate::leanh::lean_inc_ref(v_value_5508_);
        v_body_5509_ = crate::leanh::lean_ctor_get(v_e_5497_, 3);
        crate::leanh::lean_inc_ref(v_body_5509_);
        v_nondep_5510_ = crate::leanh::lean_ctor_get_uint8(
            v_e_5497_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_5497_, 4);
        v___x_5511_ = lean_expr_instantiate_rev(v_type_5507_, v_fvars_5496_);
        crate::leanh::lean_dec_ref(v_type_5507_);
        v___x_5512_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(
            v___x_5511_,
            v_a_5498_,
            v_a_5499_,
            v_a_5500_,
            v_a_5501_,
            v_a_5502_,
            v_a_5503_,
            v_a_5504_,
        );
        if crate::leanh::lean_obj_tag(v___x_5512_) == 0 {
            let mut v_a_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5513_ = crate::leanh::lean_ctor_get(v___x_5512_, 0);
            crate::leanh::lean_inc(v_a_5513_);
            crate::leanh::lean_dec_ref_known(v___x_5512_, 1);
            v___x_5514_ = lean_expr_instantiate_rev(v_value_5508_, v_fvars_5496_);
            crate::leanh::lean_dec_ref(v_value_5508_);
            v___x_5515_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                v___x_5514_,
                v_a_5498_,
                v_a_5499_,
                v_a_5500_,
                v_a_5501_,
                v_a_5502_,
                v_a_5503_,
                v_a_5504_,
            );
            if crate::leanh::lean_obj_tag(v___x_5515_) == 0 {
                let mut v_a_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5518_: u8 = 0;
                let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5516_ = crate::leanh::lean_ctor_get(v___x_5515_, 0);
                crate::leanh::lean_inc(v_a_5516_);
                crate::leanh::lean_dec_ref_known(v___x_5515_, 1);
                v___f_5517_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                crate::leanh::lean_closure_set(v___f_5517_, 0, v_fvars_5496_);
                crate::leanh::lean_closure_set(v___f_5517_, 1, v_body_5509_);
                v___x_5518_ = 0;
                v___x_5519_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_declName_5506_, v_a_5513_, v_a_5516_, v___f_5517_, v_nondep_5510_, v___x_5518_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_);
                return v___x_5519_;
            } else {
                crate::leanh::lean_dec(v_a_5513_);
                crate::leanh::lean_dec_ref(v_body_5509_);
                crate::leanh::lean_dec(v_declName_5506_);
                crate::leanh::lean_dec_ref(v_fvars_5496_);
                return v___x_5515_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_body_5509_);
            crate::leanh::lean_dec_ref(v_value_5508_);
            crate::leanh::lean_dec(v_declName_5506_);
            crate::leanh::lean_dec_ref(v_fvars_5496_);
            return v___x_5512_;
        }
    } else {
        let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5520_ = lean_expr_instantiate_rev(v_e_5497_, v_fvars_5496_);
        crate::leanh::lean_dec_ref(v_e_5497_);
        v___x_5521_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
            v___x_5520_,
            v_a_5498_,
            v_a_5499_,
            v_a_5500_,
            v_a_5501_,
            v_a_5502_,
            v_a_5503_,
            v_a_5504_,
        );
        if crate::leanh::lean_obj_tag(v___x_5521_) == 0 {
            let mut v_a_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5523_: u8 = 0;
            let mut v___x_5524_: u8 = 0;
            let mut v___x_5525_: u8 = 0;
            let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5522_ = crate::leanh::lean_ctor_get(v___x_5521_, 0);
            crate::leanh::lean_inc(v_a_5522_);
            crate::leanh::lean_dec_ref_known(v___x_5521_, 1);
            v___x_5523_ = 1;
            v___x_5524_ = 0;
            v___x_5525_ = 1;
            v___x_5526_ = l_Lean_Meta_mkLetFVars(
                v_fvars_5496_,
                v_a_5522_,
                v___x_5523_,
                v___x_5524_,
                v___x_5525_,
                v_a_5501_,
                v_a_5502_,
                v_a_5503_,
                v_a_5504_,
            );
            crate::leanh::lean_dec_ref(v_fvars_5496_);
            return v___x_5526_;
        } else {
            crate::leanh::lean_dec_ref(v_fvars_5496_);
            return v___x_5521_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(
    mut v_e_5527_: *mut crate::leanh::LeanObject,
    mut v_a_5528_: u8,
    mut v_a_5529_: *mut crate::leanh::LeanObject,
    mut v_a_5530_: *mut crate::leanh::LeanObject,
    mut v_a_5531_: *mut crate::leanh::LeanObject,
    mut v_a_5532_: *mut crate::leanh::LeanObject,
    mut v_a_5533_: *mut crate::leanh::LeanObject,
    mut v_a_5534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_a_5528_ == 0 {
        let mut v___x_5536_: u8 = 0;
        let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5536_ = 1;
        v___x_5537_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
            v_e_5527_,
            v___x_5536_,
            v_a_5529_,
            v_a_5530_,
            v_a_5531_,
            v_a_5532_,
            v_a_5533_,
            v_a_5534_,
        );
        return v___x_5537_;
    } else {
        let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5538_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
            v_e_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_,
        );
        return v___x_5538_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(
    mut v_e_5539_: *mut crate::leanh::LeanObject,
    mut v_report_5540_: u8,
    mut v_a_5541_: u8,
    mut v_a_5542_: *mut crate::leanh::LeanObject,
    mut v_a_5543_: *mut crate::leanh::LeanObject,
    mut v_a_5544_: *mut crate::leanh::LeanObject,
    mut v_a_5545_: *mut crate::leanh::LeanObject,
    mut v_a_5546_: *mut crate::leanh::LeanObject,
    mut v_a_5547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_5547_);
    crate::leanh::lean_inc_ref(v_a_5546_);
    crate::leanh::lean_inc(v_a_5545_);
    crate::leanh::lean_inc_ref(v_a_5544_);
    crate::leanh::lean_inc_ref(v_e_5539_);
    v___x_5549_ = lean_infer_type(v_e_5539_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_);
    if crate::leanh::lean_obj_tag(v___x_5549_) == 0 {
        let mut v_a_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5550_ = crate::leanh::lean_ctor_get(v___x_5549_, 0);
        crate::leanh::lean_inc(v_a_5550_);
        crate::leanh::lean_dec_ref_known(v___x_5549_, 1);
        v___x_5551_ =
            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(
                v_a_5550_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_, v_a_5546_,
                v_a_5547_,
            );
        if crate::leanh::lean_obj_tag(v___x_5551_) == 0 {
            let mut v_a_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5552_ = crate::leanh::lean_ctor_get(v___x_5551_, 0);
            crate::leanh::lean_inc(v_a_5552_);
            crate::leanh::lean_dec_ref_known(v___x_5551_, 1);
            v___x_5553_ =
                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(
                    v_e_5539_,
                    v_a_5552_,
                    v_report_5540_,
                    v_a_5542_,
                    v_a_5543_,
                    v_a_5544_,
                    v_a_5545_,
                    v_a_5546_,
                    v_a_5547_,
                );
            return v___x_5553_;
        } else {
            crate::leanh::lean_dec_ref(v_e_5539_);
            return v___x_5551_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_5539_);
        return v___x_5549_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(
    mut v_e_5554_: *mut crate::leanh::LeanObject,
    mut v_report_5555_: u8,
    mut v_a_5556_: u8,
    mut v_a_5557_: *mut crate::leanh::LeanObject,
    mut v_a_5558_: *mut crate::leanh::LeanObject,
    mut v_a_5559_: *mut crate::leanh::LeanObject,
    mut v_a_5560_: *mut crate::leanh::LeanObject,
    mut v_a_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5580_: u8 = 0;
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5592_: u8 = 0;
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v_cache_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5612_: u8 = 0;
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5622_: u8 = 0;
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5626_: u8 = 0;
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5643_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5646_: u8 = 0;
    let mut v_cache_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5651_: u8 = 0;
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5663_: u8 = 0;
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_5556_ == 0 {
                    v___x_5564_ = lean_st_ref_get(v_a_5558_);
                    v_canon_5565_ = crate::leanh::lean_ctor_get(v___x_5564_, 9);
                    crate::leanh::lean_inc_ref(v_canon_5565_);
                    crate::leanh::lean_dec(v___x_5564_);
                    v_cache_5566_ = crate::leanh::lean_ctor_get(v_canon_5565_, 0);
                    crate::leanh::lean_inc_ref(v_cache_5566_);
                    crate::leanh::lean_dec_ref(v_canon_5565_);
                    v___x_5567_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_5566_, v_e_5554_);
                    crate::leanh::lean_dec_ref(v_cache_5566_);
                    if crate::leanh::lean_obj_tag(v___x_5567_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5554_);
                        v_val_5568_ = crate::leanh::lean_ctor_get(v___x_5567_, 0);
                        v_isSharedCheck_5575_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5567_)) as u8;
                        if v_isSharedCheck_5575_ == 0 {
                            v___x_5570_ = v___x_5567_;
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5568_);
                            crate::leanh::lean_dec(v___x_5567_);
                            v___x_5570_ = crate::leanh::lean_box(0);
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5567_);
                        crate::leanh::lean_inc_ref(v_e_5554_);
                        v___x_5576_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_5554_, v_report_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_);
                        if crate::leanh::lean_obj_tag(v___x_5576_) == 0 {
                            v_a_5577_ = crate::leanh::lean_ctor_get(v___x_5576_, 0);
                            v_isSharedCheck_5614_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5576_)) as u8;
                            if v_isSharedCheck_5614_ == 0 {
                                v___x_5579_ = v___x_5576_;
                                v_isShared_5580_ = v_isSharedCheck_5614_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5577_);
                                crate::leanh::lean_dec(v___x_5576_);
                                v___x_5579_ = crate::leanh::lean_box(0);
                                v_isShared_5580_ = v_isSharedCheck_5614_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_5554_);
                            return v___x_5576_;
                        }
                    }
                } else {
                    v___x_5615_ = lean_st_ref_get(v_a_5558_);
                    v_canon_5616_ = crate::leanh::lean_ctor_get(v___x_5615_, 9);
                    crate::leanh::lean_inc_ref(v_canon_5616_);
                    crate::leanh::lean_dec(v___x_5615_);
                    v_cacheInType_5617_ = crate::leanh::lean_ctor_get(v_canon_5616_, 1);
                    crate::leanh::lean_inc_ref(v_cacheInType_5617_);
                    crate::leanh::lean_dec_ref(v_canon_5616_);
                    v___x_5618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_5617_, v_e_5554_);
                    crate::leanh::lean_dec_ref(v_cacheInType_5617_);
                    if crate::leanh::lean_obj_tag(v___x_5618_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5554_);
                        v_val_5619_ = crate::leanh::lean_ctor_get(v___x_5618_, 0);
                        v_isSharedCheck_5626_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5618_)) as u8;
                        if v_isSharedCheck_5626_ == 0 {
                            v___x_5621_ = v___x_5618_;
                            v_isShared_5622_ = v_isSharedCheck_5626_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5619_);
                            crate::leanh::lean_dec(v___x_5618_);
                            v___x_5621_ = crate::leanh::lean_box(0);
                            v_isShared_5622_ = v_isSharedCheck_5626_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5618_);
                        crate::leanh::lean_inc_ref(v_e_5554_);
                        v___x_5627_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(v_e_5554_, v_report_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_);
                        if crate::leanh::lean_obj_tag(v___x_5627_) == 0 {
                            v_a_5628_ = crate::leanh::lean_ctor_get(v___x_5627_, 0);
                            v_isSharedCheck_5665_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5627_)) as u8;
                            if v_isSharedCheck_5665_ == 0 {
                                v___x_5630_ = v___x_5627_;
                                v_isShared_5631_ = v_isSharedCheck_5665_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5628_);
                                crate::leanh::lean_dec(v___x_5627_);
                                v___x_5630_ = crate::leanh::lean_box(0);
                                v_isShared_5631_ = v_isSharedCheck_5665_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_5554_);
                            return v___x_5627_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5571_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5570_, 0);
                    v___x_5573_ = v___x_5570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_val_5568_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5573_;
            }
            3 => {
                v___x_5581_ = lean_st_ref_take(v_a_5558_);
                v_canon_5582_ = crate::leanh::lean_ctor_get(v___x_5581_, 9);
                v_share_5583_ = crate::leanh::lean_ctor_get(v___x_5581_, 0);
                v_maxFVar_5584_ = crate::leanh::lean_ctor_get(v___x_5581_, 1);
                v_proofInstInfo_5585_ = crate::leanh::lean_ctor_get(v___x_5581_, 2);
                v_inferType_5586_ = crate::leanh::lean_ctor_get(v___x_5581_, 3);
                v_getLevel_5587_ = crate::leanh::lean_ctor_get(v___x_5581_, 4);
                v_congrInfo_5588_ = crate::leanh::lean_ctor_get(v___x_5581_, 5);
                v_defEqI_5589_ = crate::leanh::lean_ctor_get(v___x_5581_, 6);
                v_extensions_5590_ = crate::leanh::lean_ctor_get(v___x_5581_, 7);
                v_issues_5591_ = crate::leanh::lean_ctor_get(v___x_5581_, 8);
                v_debug_5592_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5581_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5613_ = (!crate::leanh::lean_is_exclusive(v___x_5581_)) as u8;
                if v_isSharedCheck_5613_ == 0 {
                    v___x_5594_ = v___x_5581_;
                    v_isShared_5595_ = v_isSharedCheck_5613_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5582_);
                    crate::leanh::lean_inc(v_issues_5591_);
                    crate::leanh::lean_inc(v_extensions_5590_);
                    crate::leanh::lean_inc(v_defEqI_5589_);
                    crate::leanh::lean_inc(v_congrInfo_5588_);
                    crate::leanh::lean_inc(v_getLevel_5587_);
                    crate::leanh::lean_inc(v_inferType_5586_);
                    crate::leanh::lean_inc(v_proofInstInfo_5585_);
                    crate::leanh::lean_inc(v_maxFVar_5584_);
                    crate::leanh::lean_inc(v_share_5583_);
                    crate::leanh::lean_dec(v___x_5581_);
                    v___x_5594_ = crate::leanh::lean_box(0);
                    v_isShared_5595_ = v_isSharedCheck_5613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_cache_5596_ = crate::leanh::lean_ctor_get(v_canon_5582_, 0);
                v_cacheInType_5597_ = crate::leanh::lean_ctor_get(v_canon_5582_, 1);
                v_isSharedCheck_5612_ = (!crate::leanh::lean_is_exclusive(v_canon_5582_)) as u8;
                if v_isSharedCheck_5612_ == 0 {
                    v___x_5599_ = v_canon_5582_;
                    v_isShared_5600_ = v_isSharedCheck_5612_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_5597_);
                    crate::leanh::lean_inc(v_cache_5596_);
                    crate::leanh::lean_dec(v_canon_5582_);
                    v___x_5599_ = crate::leanh::lean_box(0);
                    v_isShared_5600_ = v_isSharedCheck_5612_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_5577_);
                v___x_5601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_5596_, v_e_5554_, v_a_5577_);
                if v_isShared_5600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5599_, 0, v___x_5601_);
                    v___x_5603_ = v___x_5599_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5611_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5611_, 0, v___x_5601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5611_, 1, v_cacheInType_5597_);
                    v___x_5603_ = v_reuseFailAlloc_5611_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5595_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5594_, 9, v___x_5603_);
                    v___x_5605_ = v___x_5594_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5610_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_share_5583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_maxFVar_5584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 2, v_proofInstInfo_5585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 3, v_inferType_5586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 4, v_getLevel_5587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 5, v_congrInfo_5588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 6, v_defEqI_5589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 7, v_extensions_5590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 8, v_issues_5591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 9, v___x_5603_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5592_,
                    );
                    v___x_5605_ = v_reuseFailAlloc_5610_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5606_ = lean_st_ref_set(v_a_5558_, v___x_5605_);
                if v_isShared_5580_ == 0 {
                    v___x_5608_ = v___x_5579_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5577_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5608_;
            }
            9 => {
                if v_isShared_5622_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5621_, 0);
                    v___x_5624_ = v___x_5621_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_val_5619_);
                    v___x_5624_ = v_reuseFailAlloc_5625_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5624_;
            }
            11 => {
                v___x_5632_ = lean_st_ref_take(v_a_5558_);
                v_canon_5633_ = crate::leanh::lean_ctor_get(v___x_5632_, 9);
                v_share_5634_ = crate::leanh::lean_ctor_get(v___x_5632_, 0);
                v_maxFVar_5635_ = crate::leanh::lean_ctor_get(v___x_5632_, 1);
                v_proofInstInfo_5636_ = crate::leanh::lean_ctor_get(v___x_5632_, 2);
                v_inferType_5637_ = crate::leanh::lean_ctor_get(v___x_5632_, 3);
                v_getLevel_5638_ = crate::leanh::lean_ctor_get(v___x_5632_, 4);
                v_congrInfo_5639_ = crate::leanh::lean_ctor_get(v___x_5632_, 5);
                v_defEqI_5640_ = crate::leanh::lean_ctor_get(v___x_5632_, 6);
                v_extensions_5641_ = crate::leanh::lean_ctor_get(v___x_5632_, 7);
                v_issues_5642_ = crate::leanh::lean_ctor_get(v___x_5632_, 8);
                v_debug_5643_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5632_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5664_ = (!crate::leanh::lean_is_exclusive(v___x_5632_)) as u8;
                if v_isSharedCheck_5664_ == 0 {
                    v___x_5645_ = v___x_5632_;
                    v_isShared_5646_ = v_isSharedCheck_5664_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5633_);
                    crate::leanh::lean_inc(v_issues_5642_);
                    crate::leanh::lean_inc(v_extensions_5641_);
                    crate::leanh::lean_inc(v_defEqI_5640_);
                    crate::leanh::lean_inc(v_congrInfo_5639_);
                    crate::leanh::lean_inc(v_getLevel_5638_);
                    crate::leanh::lean_inc(v_inferType_5637_);
                    crate::leanh::lean_inc(v_proofInstInfo_5636_);
                    crate::leanh::lean_inc(v_maxFVar_5635_);
                    crate::leanh::lean_inc(v_share_5634_);
                    crate::leanh::lean_dec(v___x_5632_);
                    v___x_5645_ = crate::leanh::lean_box(0);
                    v_isShared_5646_ = v_isSharedCheck_5664_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_cache_5647_ = crate::leanh::lean_ctor_get(v_canon_5633_, 0);
                v_cacheInType_5648_ = crate::leanh::lean_ctor_get(v_canon_5633_, 1);
                v_isSharedCheck_5663_ = (!crate::leanh::lean_is_exclusive(v_canon_5633_)) as u8;
                if v_isSharedCheck_5663_ == 0 {
                    v___x_5650_ = v_canon_5633_;
                    v_isShared_5651_ = v_isSharedCheck_5663_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_5648_);
                    crate::leanh::lean_inc(v_cache_5647_);
                    crate::leanh::lean_dec(v_canon_5633_);
                    v___x_5650_ = crate::leanh::lean_box(0);
                    v_isShared_5651_ = v_isSharedCheck_5663_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc(v_a_5628_);
                v___x_5652_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_5648_, v_e_5554_, v_a_5628_);
                if v_isShared_5651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5650_, 1, v___x_5652_);
                    v___x_5654_ = v___x_5650_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_cache_5647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5662_, 1, v___x_5652_);
                    v___x_5654_ = v_reuseFailAlloc_5662_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5645_, 9, v___x_5654_);
                    v___x_5656_ = v___x_5645_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5661_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_share_5634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 1, v_maxFVar_5635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 2, v_proofInstInfo_5636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 3, v_inferType_5637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 4, v_getLevel_5638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 5, v_congrInfo_5639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 6, v_defEqI_5640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 7, v_extensions_5641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 8, v_issues_5642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5661_, 9, v___x_5654_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5661_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5643_,
                    );
                    v___x_5656_ = v_reuseFailAlloc_5661_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_5657_ = lean_st_ref_set(v_a_5558_, v___x_5656_);
                if v_isShared_5631_ == 0 {
                    v___x_5659_ = v___x_5630_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5628_);
                    v___x_5659_ = v_reuseFailAlloc_5660_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5680_ = crate::leanh::lean_box(0);
    v___x_5681_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__1;
    v___x_5682_ = l_Lean_mkConst(v___x_5681_, v___x_5680_);
    return v___x_5682_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(
    mut v_g_5683_: *mut crate::leanh::LeanObject,
    mut v_prop_5684_: *mut crate::leanh::LeanObject,
    mut v_inst_5685_: *mut crate::leanh::LeanObject,
    mut v_e_5686_: *mut crate::leanh::LeanObject,
    mut v_a_5687_: u8,
    mut v_a_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___y_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5702_: u8 = 0;
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: u8 = 0;
    let mut v___x_5719_: u8 = 0;
    let mut v_val_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5724_: u8 = 0;
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5728_: u8 = 0;
    let mut v___x_5729_: u8 = 0;
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_prop_5684_);
                v___x_5695_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                    v_prop_5684_,
                    v_a_5687_,
                    v_a_5688_,
                    v_a_5689_,
                    v_a_5690_,
                    v_a_5691_,
                    v_a_5692_,
                    v_a_5693_,
                );
                if crate::leanh::lean_obj_tag(v___x_5695_) == 0 {
                    v_a_5696_ = crate::leanh::lean_ctor_get(v___x_5695_, 0);
                    v_isSharedCheck_5731_ = (!crate::leanh::lean_is_exclusive(v___x_5695_)) as u8;
                    if v_isSharedCheck_5731_ == 0 {
                        v___x_5698_ = v___x_5695_;
                        v_isShared_5699_ = v_isSharedCheck_5731_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5696_);
                        crate::leanh::lean_dec(v___x_5695_);
                        v___x_5698_ = crate::leanh::lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5731_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5686_);
                    crate::leanh::lean_dec_ref(v_inst_5685_);
                    crate::leanh::lean_dec_ref(v_prop_5684_);
                    crate::leanh::lean_dec_ref(v_g_5683_);
                    return v___x_5695_;
                }
            }
            1 => {
                v___x_5710_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___closed__2);
                crate::leanh::lean_inc(v_a_5696_);
                v___x_5711_ = l_Lean_Expr_app___override(v___x_5710_, v_a_5696_);
                if v_a_5687_ == 0 {
                    v___x_5712_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_5711_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5712_) == 0 {
                        v_a_5713_ = crate::leanh::lean_ctor_get(v___x_5712_, 0);
                        crate::leanh::lean_inc(v_a_5713_);
                        crate::leanh::lean_dec_ref_known(v___x_5712_, 1);
                        if crate::leanh::lean_obj_tag(v_a_5713_) == 0 {
                            crate::leanh::lean_inc_ref(v_inst_5685_);
                            v___y_5715_ = v_inst_5685_;
                            state = 5;
                            continue;
                        } else {
                            v_val_5720_ = crate::leanh::lean_ctor_get(v_a_5713_, 0);
                            crate::leanh::lean_inc(v_val_5720_);
                            crate::leanh::lean_dec_ref_known(v_a_5713_, 1);
                            v___y_5715_ = v_val_5720_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5698_);
                        crate::leanh::lean_dec(v_a_5696_);
                        crate::leanh::lean_dec_ref(v_e_5686_);
                        crate::leanh::lean_dec_ref(v_inst_5685_);
                        crate::leanh::lean_dec_ref(v_prop_5684_);
                        crate::leanh::lean_dec_ref(v_g_5683_);
                        v_a_5721_ = crate::leanh::lean_ctor_get(v___x_5712_, 0);
                        v_isSharedCheck_5728_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5712_)) as u8;
                        if v_isSharedCheck_5728_ == 0 {
                            v___x_5723_ = v___x_5712_;
                            v_isShared_5724_ = v_isSharedCheck_5728_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5721_);
                            crate::leanh::lean_dec(v___x_5712_);
                            v___x_5723_ = crate::leanh::lean_box(0);
                            v_isShared_5724_ = v_isSharedCheck_5728_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5698_);
                    crate::leanh::lean_dec(v_a_5696_);
                    crate::leanh::lean_dec_ref(v_e_5686_);
                    crate::leanh::lean_dec_ref(v_prop_5684_);
                    crate::leanh::lean_dec_ref(v_g_5683_);
                    v___x_5729_ = 0;
                    v___x_5730_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_inst_5685_, v___x_5711_, v___x_5729_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_);
                    return v___x_5730_;
                }
            }
            2 => {
                if v___y_5702_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_5686_);
                    v___x_5703_ = l_Lean_mkAppB(v_g_5683_, v_a_5696_, v___y_5701_);
                    if v_isShared_5699_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5698_, 0, v___x_5703_);
                        v___x_5705_ = v___x_5698_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5706_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5706_, 0, v___x_5703_);
                        v___x_5705_ = v_reuseFailAlloc_5706_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5701_);
                    crate::leanh::lean_dec(v_a_5696_);
                    crate::leanh::lean_dec_ref(v_g_5683_);
                    if v_isShared_5699_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5698_, 0, v_e_5686_);
                        v___x_5708_ = v___x_5698_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5709_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_e_5686_);
                        v___x_5708_ = v_reuseFailAlloc_5709_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5705_;
            }
            4 => {
                return v___x_5708_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v_inst_5685_);
                v___x_5716_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_checkDefEqInst(
                    v_inst_5685_,
                    v___y_5715_,
                    v_a_5688_,
                    v_a_5689_,
                    v_a_5690_,
                    v_a_5691_,
                    v_a_5692_,
                    v_a_5693_,
                );
                if crate::leanh::lean_obj_tag(v___x_5716_) == 0 {
                    v_a_5717_ = crate::leanh::lean_ctor_get(v___x_5716_, 0);
                    crate::leanh::lean_inc(v_a_5717_);
                    crate::leanh::lean_dec_ref_known(v___x_5716_, 1);
                    v___x_5718_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_prop_5684_,
                            v_a_5696_,
                        );
                    crate::leanh::lean_dec_ref(v_prop_5684_);
                    if v___x_5718_ == 0 {
                        crate::leanh::lean_dec_ref(v_inst_5685_);
                        v___y_5701_ = v_a_5717_;
                        v___y_5702_ = v___x_5718_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5719_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_inst_5685_,
                                v_a_5717_,
                            );
                        crate::leanh::lean_dec_ref(v_inst_5685_);
                        v___y_5701_ = v_a_5717_;
                        v___y_5702_ = v___x_5719_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5698_);
                    crate::leanh::lean_dec(v_a_5696_);
                    crate::leanh::lean_dec_ref(v_e_5686_);
                    crate::leanh::lean_dec_ref(v_inst_5685_);
                    crate::leanh::lean_dec_ref(v_prop_5684_);
                    crate::leanh::lean_dec_ref(v_g_5683_);
                    return v___x_5716_;
                }
            }
            6 => {
                if v_isShared_5724_ == 0 {
                    v___x_5726_ = v___x_5723_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5721_);
                    v___x_5726_ = v_reuseFailAlloc_5727_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(
    mut v_g_5732_: *mut crate::leanh::LeanObject,
    mut v_prop_5733_: *mut crate::leanh::LeanObject,
    mut v_h_5734_: *mut crate::leanh::LeanObject,
    mut v_e_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: u8,
    mut v_a_5737_: *mut crate::leanh::LeanObject,
    mut v_a_5738_: *mut crate::leanh::LeanObject,
    mut v_a_5739_: *mut crate::leanh::LeanObject,
    mut v_a_5740_: *mut crate::leanh::LeanObject,
    mut v_a_5741_: *mut crate::leanh::LeanObject,
    mut v_a_5742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5751_: u8 = 0;
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5755_: u8 = 0;
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5760_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5772_: u8 = 0;
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v_cache_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5780_: u8 = 0;
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut v_isSharedCheck_5793_: u8 = 0;
    let mut v_isSharedCheck_5794_: u8 = 0;
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5802_: u8 = 0;
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5806_: u8 = 0;
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5811_: u8 = 0;
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5823_: u8 = 0;
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5826_: u8 = 0;
    let mut v_cache_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5831_: u8 = 0;
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_isSharedCheck_5844_: u8 = 0;
    let mut v_isSharedCheck_5845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_5736_ == 0 {
                    v___x_5744_ = lean_st_ref_get(v_a_5738_);
                    v_canon_5745_ = crate::leanh::lean_ctor_get(v___x_5744_, 9);
                    crate::leanh::lean_inc_ref(v_canon_5745_);
                    crate::leanh::lean_dec(v___x_5744_);
                    v_cache_5746_ = crate::leanh::lean_ctor_get(v_canon_5745_, 0);
                    crate::leanh::lean_inc_ref(v_cache_5746_);
                    crate::leanh::lean_dec_ref(v_canon_5745_);
                    v___x_5747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_5746_, v_e_5735_);
                    crate::leanh::lean_dec_ref(v_cache_5746_);
                    if crate::leanh::lean_obj_tag(v___x_5747_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5735_);
                        crate::leanh::lean_dec_ref(v_h_5734_);
                        crate::leanh::lean_dec_ref(v_prop_5733_);
                        crate::leanh::lean_dec_ref(v_g_5732_);
                        v_val_5748_ = crate::leanh::lean_ctor_get(v___x_5747_, 0);
                        v_isSharedCheck_5755_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5747_)) as u8;
                        if v_isSharedCheck_5755_ == 0 {
                            v___x_5750_ = v___x_5747_;
                            v_isShared_5751_ = v_isSharedCheck_5755_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5748_);
                            crate::leanh::lean_dec(v___x_5747_);
                            v___x_5750_ = crate::leanh::lean_box(0);
                            v_isShared_5751_ = v_isSharedCheck_5755_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5747_);
                        crate::leanh::lean_inc_ref(v_e_5735_);
                        v___x_5756_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_5732_, v_prop_5733_, v_h_5734_, v_e_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
                        if crate::leanh::lean_obj_tag(v___x_5756_) == 0 {
                            v_a_5757_ = crate::leanh::lean_ctor_get(v___x_5756_, 0);
                            v_isSharedCheck_5794_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5794_ == 0 {
                                v___x_5759_ = v___x_5756_;
                                v_isShared_5760_ = v_isSharedCheck_5794_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5757_);
                                crate::leanh::lean_dec(v___x_5756_);
                                v___x_5759_ = crate::leanh::lean_box(0);
                                v_isShared_5760_ = v_isSharedCheck_5794_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_5735_);
                            return v___x_5756_;
                        }
                    }
                } else {
                    v___x_5795_ = lean_st_ref_get(v_a_5738_);
                    v_canon_5796_ = crate::leanh::lean_ctor_get(v___x_5795_, 9);
                    crate::leanh::lean_inc_ref(v_canon_5796_);
                    crate::leanh::lean_dec(v___x_5795_);
                    v_cacheInType_5797_ = crate::leanh::lean_ctor_get(v_canon_5796_, 1);
                    crate::leanh::lean_inc_ref(v_cacheInType_5797_);
                    crate::leanh::lean_dec_ref(v_canon_5796_);
                    v___x_5798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_5797_, v_e_5735_);
                    crate::leanh::lean_dec_ref(v_cacheInType_5797_);
                    if crate::leanh::lean_obj_tag(v___x_5798_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5735_);
                        crate::leanh::lean_dec_ref(v_h_5734_);
                        crate::leanh::lean_dec_ref(v_prop_5733_);
                        crate::leanh::lean_dec_ref(v_g_5732_);
                        v_val_5799_ = crate::leanh::lean_ctor_get(v___x_5798_, 0);
                        v_isSharedCheck_5806_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5798_)) as u8;
                        if v_isSharedCheck_5806_ == 0 {
                            v___x_5801_ = v___x_5798_;
                            v_isShared_5802_ = v_isSharedCheck_5806_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5799_);
                            crate::leanh::lean_dec(v___x_5798_);
                            v___x_5801_ = crate::leanh::lean_box(0);
                            v_isShared_5802_ = v_isSharedCheck_5806_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5798_);
                        crate::leanh::lean_inc_ref(v_e_5735_);
                        v___x_5807_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_g_5732_, v_prop_5733_, v_h_5734_, v_e_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
                        if crate::leanh::lean_obj_tag(v___x_5807_) == 0 {
                            v_a_5808_ = crate::leanh::lean_ctor_get(v___x_5807_, 0);
                            v_isSharedCheck_5845_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5807_)) as u8;
                            if v_isSharedCheck_5845_ == 0 {
                                v___x_5810_ = v___x_5807_;
                                v_isShared_5811_ = v_isSharedCheck_5845_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5808_);
                                crate::leanh::lean_dec(v___x_5807_);
                                v___x_5810_ = crate::leanh::lean_box(0);
                                v_isShared_5811_ = v_isSharedCheck_5845_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_5735_);
                            return v___x_5807_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5751_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5750_, 0);
                    v___x_5753_ = v___x_5750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_val_5748_);
                    v___x_5753_ = v_reuseFailAlloc_5754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5753_;
            }
            3 => {
                v___x_5761_ = lean_st_ref_take(v_a_5738_);
                v_canon_5762_ = crate::leanh::lean_ctor_get(v___x_5761_, 9);
                v_share_5763_ = crate::leanh::lean_ctor_get(v___x_5761_, 0);
                v_maxFVar_5764_ = crate::leanh::lean_ctor_get(v___x_5761_, 1);
                v_proofInstInfo_5765_ = crate::leanh::lean_ctor_get(v___x_5761_, 2);
                v_inferType_5766_ = crate::leanh::lean_ctor_get(v___x_5761_, 3);
                v_getLevel_5767_ = crate::leanh::lean_ctor_get(v___x_5761_, 4);
                v_congrInfo_5768_ = crate::leanh::lean_ctor_get(v___x_5761_, 5);
                v_defEqI_5769_ = crate::leanh::lean_ctor_get(v___x_5761_, 6);
                v_extensions_5770_ = crate::leanh::lean_ctor_get(v___x_5761_, 7);
                v_issues_5771_ = crate::leanh::lean_ctor_get(v___x_5761_, 8);
                v_debug_5772_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5793_ = (!crate::leanh::lean_is_exclusive(v___x_5761_)) as u8;
                if v_isSharedCheck_5793_ == 0 {
                    v___x_5774_ = v___x_5761_;
                    v_isShared_5775_ = v_isSharedCheck_5793_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5762_);
                    crate::leanh::lean_inc(v_issues_5771_);
                    crate::leanh::lean_inc(v_extensions_5770_);
                    crate::leanh::lean_inc(v_defEqI_5769_);
                    crate::leanh::lean_inc(v_congrInfo_5768_);
                    crate::leanh::lean_inc(v_getLevel_5767_);
                    crate::leanh::lean_inc(v_inferType_5766_);
                    crate::leanh::lean_inc(v_proofInstInfo_5765_);
                    crate::leanh::lean_inc(v_maxFVar_5764_);
                    crate::leanh::lean_inc(v_share_5763_);
                    crate::leanh::lean_dec(v___x_5761_);
                    v___x_5774_ = crate::leanh::lean_box(0);
                    v_isShared_5775_ = v_isSharedCheck_5793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_cache_5776_ = crate::leanh::lean_ctor_get(v_canon_5762_, 0);
                v_cacheInType_5777_ = crate::leanh::lean_ctor_get(v_canon_5762_, 1);
                v_isSharedCheck_5792_ = (!crate::leanh::lean_is_exclusive(v_canon_5762_)) as u8;
                if v_isSharedCheck_5792_ == 0 {
                    v___x_5779_ = v_canon_5762_;
                    v_isShared_5780_ = v_isSharedCheck_5792_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_5777_);
                    crate::leanh::lean_inc(v_cache_5776_);
                    crate::leanh::lean_dec(v_canon_5762_);
                    v___x_5779_ = crate::leanh::lean_box(0);
                    v_isShared_5780_ = v_isSharedCheck_5792_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_5757_);
                v___x_5781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_5776_, v_e_5735_, v_a_5757_);
                if v_isShared_5780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5779_, 0, v___x_5781_);
                    v___x_5783_ = v___x_5779_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_cacheInType_5777_);
                    v___x_5783_ = v_reuseFailAlloc_5791_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5774_, 9, v___x_5783_);
                    v___x_5785_ = v___x_5774_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5790_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_share_5763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 1, v_maxFVar_5764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 2, v_proofInstInfo_5765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 3, v_inferType_5766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 4, v_getLevel_5767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 5, v_congrInfo_5768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 6, v_defEqI_5769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 7, v_extensions_5770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 8, v_issues_5771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 9, v___x_5783_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5790_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5772_,
                    );
                    v___x_5785_ = v_reuseFailAlloc_5790_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5786_ = lean_st_ref_set(v_a_5738_, v___x_5785_);
                if v_isShared_5760_ == 0 {
                    v___x_5788_ = v___x_5759_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5789_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_a_5757_);
                    v___x_5788_ = v_reuseFailAlloc_5789_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5788_;
            }
            9 => {
                if v_isShared_5802_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5801_, 0);
                    v___x_5804_ = v___x_5801_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_val_5799_);
                    v___x_5804_ = v_reuseFailAlloc_5805_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5804_;
            }
            11 => {
                v___x_5812_ = lean_st_ref_take(v_a_5738_);
                v_canon_5813_ = crate::leanh::lean_ctor_get(v___x_5812_, 9);
                v_share_5814_ = crate::leanh::lean_ctor_get(v___x_5812_, 0);
                v_maxFVar_5815_ = crate::leanh::lean_ctor_get(v___x_5812_, 1);
                v_proofInstInfo_5816_ = crate::leanh::lean_ctor_get(v___x_5812_, 2);
                v_inferType_5817_ = crate::leanh::lean_ctor_get(v___x_5812_, 3);
                v_getLevel_5818_ = crate::leanh::lean_ctor_get(v___x_5812_, 4);
                v_congrInfo_5819_ = crate::leanh::lean_ctor_get(v___x_5812_, 5);
                v_defEqI_5820_ = crate::leanh::lean_ctor_get(v___x_5812_, 6);
                v_extensions_5821_ = crate::leanh::lean_ctor_get(v___x_5812_, 7);
                v_issues_5822_ = crate::leanh::lean_ctor_get(v___x_5812_, 8);
                v_debug_5823_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5812_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5844_ = (!crate::leanh::lean_is_exclusive(v___x_5812_)) as u8;
                if v_isSharedCheck_5844_ == 0 {
                    v___x_5825_ = v___x_5812_;
                    v_isShared_5826_ = v_isSharedCheck_5844_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5813_);
                    crate::leanh::lean_inc(v_issues_5822_);
                    crate::leanh::lean_inc(v_extensions_5821_);
                    crate::leanh::lean_inc(v_defEqI_5820_);
                    crate::leanh::lean_inc(v_congrInfo_5819_);
                    crate::leanh::lean_inc(v_getLevel_5818_);
                    crate::leanh::lean_inc(v_inferType_5817_);
                    crate::leanh::lean_inc(v_proofInstInfo_5816_);
                    crate::leanh::lean_inc(v_maxFVar_5815_);
                    crate::leanh::lean_inc(v_share_5814_);
                    crate::leanh::lean_dec(v___x_5812_);
                    v___x_5825_ = crate::leanh::lean_box(0);
                    v_isShared_5826_ = v_isSharedCheck_5844_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_cache_5827_ = crate::leanh::lean_ctor_get(v_canon_5813_, 0);
                v_cacheInType_5828_ = crate::leanh::lean_ctor_get(v_canon_5813_, 1);
                v_isSharedCheck_5843_ = (!crate::leanh::lean_is_exclusive(v_canon_5813_)) as u8;
                if v_isSharedCheck_5843_ == 0 {
                    v___x_5830_ = v_canon_5813_;
                    v_isShared_5831_ = v_isSharedCheck_5843_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_5828_);
                    crate::leanh::lean_inc(v_cache_5827_);
                    crate::leanh::lean_dec(v_canon_5813_);
                    v___x_5830_ = crate::leanh::lean_box(0);
                    v_isShared_5831_ = v_isSharedCheck_5843_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc(v_a_5808_);
                v___x_5832_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_5828_, v_e_5735_, v_a_5808_);
                if v_isShared_5831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5830_, 1, v___x_5832_);
                    v___x_5834_ = v___x_5830_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5842_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_cache_5827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 1, v___x_5832_);
                    v___x_5834_ = v_reuseFailAlloc_5842_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5825_, 9, v___x_5834_);
                    v___x_5836_ = v___x_5825_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5841_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_share_5814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 1, v_maxFVar_5815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 2, v_proofInstInfo_5816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 3, v_inferType_5817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 4, v_getLevel_5818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 5, v_congrInfo_5819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 6, v_defEqI_5820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 7, v_extensions_5821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 8, v_issues_5822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 9, v___x_5834_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5841_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5823_,
                    );
                    v___x_5836_ = v_reuseFailAlloc_5841_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_5837_ = lean_st_ref_set(v_a_5738_, v___x_5836_);
                if v_isShared_5811_ == 0 {
                    v___x_5839_ = v___x_5810_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5840_, 0, v_a_5808_);
                    v___x_5839_ = v_reuseFailAlloc_5840_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(
    mut v_g_5846_: *mut crate::leanh::LeanObject,
    mut v_prop_5847_: *mut crate::leanh::LeanObject,
    mut v_h_5848_: *mut crate::leanh::LeanObject,
    mut v_e_5849_: *mut crate::leanh::LeanObject,
    mut v_a_5850_: u8,
    mut v_a_5851_: *mut crate::leanh::LeanObject,
    mut v_a_5852_: *mut crate::leanh::LeanObject,
    mut v_a_5853_: *mut crate::leanh::LeanObject,
    mut v_a_5854_: *mut crate::leanh::LeanObject,
    mut v_a_5855_: *mut crate::leanh::LeanObject,
    mut v_a_5856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5871_: u8 = 0;
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v_cache_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5879_: u8 = 0;
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_isSharedCheck_5890_: u8 = 0;
    let mut v___y_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5896_: u8 = 0;
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5908_: u8 = 0;
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5911_: u8 = 0;
    let mut v_cache_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut v_isSharedCheck_5929_: u8 = 0;
    let mut v_isSharedCheck_5930_: u8 = 0;
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5938_: u8 = 0;
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5942_: u8 = 0;
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: u8 = 0;
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: u8 = 0;
    let mut v___x_5954_: u8 = 0;
    let mut v_val_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5959_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5963_: u8 = 0;
    let mut v_a_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5972_: u8 = 0;
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5976_: u8 = 0;
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: u8 = 0;
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_5850_ == 0 {
                    v___x_5931_ = lean_st_ref_get(v_a_5852_);
                    v_canon_5932_ = crate::leanh::lean_ctor_get(v___x_5931_, 9);
                    crate::leanh::lean_inc_ref(v_canon_5932_);
                    crate::leanh::lean_dec(v___x_5931_);
                    v_cache_5933_ = crate::leanh::lean_ctor_get(v_canon_5932_, 0);
                    crate::leanh::lean_inc_ref(v_cache_5933_);
                    crate::leanh::lean_dec_ref(v_canon_5932_);
                    v___x_5934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_5933_, v_e_5849_);
                    crate::leanh::lean_dec_ref(v_cache_5933_);
                    if crate::leanh::lean_obj_tag(v___x_5934_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5849_);
                        crate::leanh::lean_dec_ref(v_h_5848_);
                        crate::leanh::lean_dec_ref(v_prop_5847_);
                        crate::leanh::lean_dec_ref(v_g_5846_);
                        v_val_5935_ = crate::leanh::lean_ctor_get(v___x_5934_, 0);
                        v_isSharedCheck_5942_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5934_)) as u8;
                        if v_isSharedCheck_5942_ == 0 {
                            v___x_5937_ = v___x_5934_;
                            v_isShared_5938_ = v_isSharedCheck_5942_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5935_);
                            crate::leanh::lean_dec(v___x_5934_);
                            v___x_5937_ = crate::leanh::lean_box(0);
                            v_isShared_5938_ = v_isSharedCheck_5942_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5934_);
                        crate::leanh::lean_inc_ref(v_prop_5847_);
                        v___x_5943_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                            v_prop_5847_,
                            v_a_5850_,
                            v_a_5851_,
                            v_a_5852_,
                            v_a_5853_,
                            v_a_5854_,
                            v_a_5855_,
                            v_a_5856_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5943_) == 0 {
                            v_a_5944_ = crate::leanh::lean_ctor_get(v___x_5943_, 0);
                            crate::leanh::lean_inc_n(v_a_5944_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_5943_, 1);
                            v___x_5945_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                                v_a_5944_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5945_) == 0 {
                                v_a_5946_ = crate::leanh::lean_ctor_get(v___x_5945_, 0);
                                crate::leanh::lean_inc(v_a_5946_);
                                crate::leanh::lean_dec_ref_known(v___x_5945_, 1);
                                if crate::leanh::lean_obj_tag(v_a_5946_) == 0 {
                                    crate::leanh::lean_inc_ref(v_h_5848_);
                                    v___y_5952_ = v_h_5848_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_val_5955_ = crate::leanh::lean_ctor_get(v_a_5946_, 0);
                                    crate::leanh::lean_inc(v_val_5955_);
                                    crate::leanh::lean_dec_ref_known(v_a_5946_, 1);
                                    v___y_5952_ = v_val_5955_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5944_);
                                crate::leanh::lean_dec_ref(v_e_5849_);
                                crate::leanh::lean_dec_ref(v_h_5848_);
                                crate::leanh::lean_dec_ref(v_prop_5847_);
                                crate::leanh::lean_dec_ref(v_g_5846_);
                                v_a_5956_ = crate::leanh::lean_ctor_get(v___x_5945_, 0);
                                v_isSharedCheck_5963_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5945_)) as u8;
                                if v_isSharedCheck_5963_ == 0 {
                                    v___x_5958_ = v___x_5945_;
                                    v_isShared_5959_ = v_isSharedCheck_5963_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5956_);
                                    crate::leanh::lean_dec(v___x_5945_);
                                    v___x_5958_ = crate::leanh::lean_box(0);
                                    v_isShared_5959_ = v_isSharedCheck_5963_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_h_5848_);
                            crate::leanh::lean_dec_ref(v_prop_5847_);
                            crate::leanh::lean_dec_ref(v_g_5846_);
                            if crate::leanh::lean_obj_tag(v___x_5943_) == 0 {
                                v_a_5964_ = crate::leanh::lean_ctor_get(v___x_5943_, 0);
                                crate::leanh::lean_inc(v_a_5964_);
                                crate::leanh::lean_dec_ref_known(v___x_5943_, 1);
                                v_a_5859_ = v_a_5964_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_e_5849_);
                                return v___x_5943_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_g_5846_);
                    v___x_5965_ = lean_st_ref_get(v_a_5852_);
                    v_canon_5966_ = crate::leanh::lean_ctor_get(v___x_5965_, 9);
                    crate::leanh::lean_inc_ref(v_canon_5966_);
                    crate::leanh::lean_dec(v___x_5965_);
                    v_cacheInType_5967_ = crate::leanh::lean_ctor_get(v_canon_5966_, 1);
                    crate::leanh::lean_inc_ref(v_cacheInType_5967_);
                    crate::leanh::lean_dec_ref(v_canon_5966_);
                    v___x_5968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_5967_, v_e_5849_);
                    crate::leanh::lean_dec_ref(v_cacheInType_5967_);
                    if crate::leanh::lean_obj_tag(v___x_5968_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5849_);
                        crate::leanh::lean_dec_ref(v_h_5848_);
                        crate::leanh::lean_dec_ref(v_prop_5847_);
                        v_val_5969_ = crate::leanh::lean_ctor_get(v___x_5968_, 0);
                        v_isSharedCheck_5976_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5968_)) as u8;
                        if v_isSharedCheck_5976_ == 0 {
                            v___x_5971_ = v___x_5968_;
                            v_isShared_5972_ = v_isSharedCheck_5976_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5969_);
                            crate::leanh::lean_dec(v___x_5968_);
                            v___x_5971_ = crate::leanh::lean_box(0);
                            v_isShared_5972_ = v_isSharedCheck_5976_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5968_);
                        v___x_5977_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                            v_prop_5847_,
                            v_a_5850_,
                            v_a_5851_,
                            v_a_5852_,
                            v_a_5853_,
                            v_a_5854_,
                            v_a_5855_,
                            v_a_5856_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5977_) == 0 {
                            v_a_5978_ = crate::leanh::lean_ctor_get(v___x_5977_, 0);
                            crate::leanh::lean_inc(v_a_5978_);
                            crate::leanh::lean_dec_ref_known(v___x_5977_, 1);
                            v___x_5979_ = 0;
                            v___x_5980_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstCore___redArg(v_h_5848_, v_a_5978_, v___x_5979_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_);
                            v___y_5892_ = v___x_5980_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_h_5848_);
                            v___y_5892_ = v___x_5977_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5860_ = lean_st_ref_take(v_a_5852_);
                v_canon_5861_ = crate::leanh::lean_ctor_get(v___x_5860_, 9);
                v_share_5862_ = crate::leanh::lean_ctor_get(v___x_5860_, 0);
                v_maxFVar_5863_ = crate::leanh::lean_ctor_get(v___x_5860_, 1);
                v_proofInstInfo_5864_ = crate::leanh::lean_ctor_get(v___x_5860_, 2);
                v_inferType_5865_ = crate::leanh::lean_ctor_get(v___x_5860_, 3);
                v_getLevel_5866_ = crate::leanh::lean_ctor_get(v___x_5860_, 4);
                v_congrInfo_5867_ = crate::leanh::lean_ctor_get(v___x_5860_, 5);
                v_defEqI_5868_ = crate::leanh::lean_ctor_get(v___x_5860_, 6);
                v_extensions_5869_ = crate::leanh::lean_ctor_get(v___x_5860_, 7);
                v_issues_5870_ = crate::leanh::lean_ctor_get(v___x_5860_, 8);
                v_debug_5871_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5860_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5890_ = (!crate::leanh::lean_is_exclusive(v___x_5860_)) as u8;
                if v_isSharedCheck_5890_ == 0 {
                    v___x_5873_ = v___x_5860_;
                    v_isShared_5874_ = v_isSharedCheck_5890_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5861_);
                    crate::leanh::lean_inc(v_issues_5870_);
                    crate::leanh::lean_inc(v_extensions_5869_);
                    crate::leanh::lean_inc(v_defEqI_5868_);
                    crate::leanh::lean_inc(v_congrInfo_5867_);
                    crate::leanh::lean_inc(v_getLevel_5866_);
                    crate::leanh::lean_inc(v_inferType_5865_);
                    crate::leanh::lean_inc(v_proofInstInfo_5864_);
                    crate::leanh::lean_inc(v_maxFVar_5863_);
                    crate::leanh::lean_inc(v_share_5862_);
                    crate::leanh::lean_dec(v___x_5860_);
                    v___x_5873_ = crate::leanh::lean_box(0);
                    v_isShared_5874_ = v_isSharedCheck_5890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_cache_5875_ = crate::leanh::lean_ctor_get(v_canon_5861_, 0);
                v_cacheInType_5876_ = crate::leanh::lean_ctor_get(v_canon_5861_, 1);
                v_isSharedCheck_5889_ = (!crate::leanh::lean_is_exclusive(v_canon_5861_)) as u8;
                if v_isSharedCheck_5889_ == 0 {
                    v___x_5878_ = v_canon_5861_;
                    v_isShared_5879_ = v_isSharedCheck_5889_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_5876_);
                    crate::leanh::lean_inc(v_cache_5875_);
                    crate::leanh::lean_dec(v_canon_5861_);
                    v___x_5878_ = crate::leanh::lean_box(0);
                    v_isShared_5879_ = v_isSharedCheck_5889_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_a_5859_);
                v___x_5880_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_5875_, v_e_5849_, v_a_5859_);
                if v_isShared_5879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5878_, 0, v___x_5880_);
                    v___x_5882_ = v___x_5878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 0, v___x_5880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 1, v_cacheInType_5876_);
                    v___x_5882_ = v_reuseFailAlloc_5888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5873_, 9, v___x_5882_);
                    v___x_5884_ = v___x_5873_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5887_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_share_5862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 1, v_maxFVar_5863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 2, v_proofInstInfo_5864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 3, v_inferType_5865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 4, v_getLevel_5866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 5, v_congrInfo_5867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 6, v_defEqI_5868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 7, v_extensions_5869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 8, v_issues_5870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 9, v___x_5882_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5887_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5871_,
                    );
                    v___x_5884_ = v_reuseFailAlloc_5887_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5885_ = lean_st_ref_set(v_a_5852_, v___x_5884_);
                v___x_5886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5886_, 0, v_a_5859_);
                return v___x_5886_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_5892_) == 0 {
                    v_a_5893_ = crate::leanh::lean_ctor_get(v___y_5892_, 0);
                    v_isSharedCheck_5930_ = (!crate::leanh::lean_is_exclusive(v___y_5892_)) as u8;
                    if v_isSharedCheck_5930_ == 0 {
                        v___x_5895_ = v___y_5892_;
                        v_isShared_5896_ = v_isSharedCheck_5930_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5893_);
                        crate::leanh::lean_dec(v___y_5892_);
                        v___x_5895_ = crate::leanh::lean_box(0);
                        v_isShared_5896_ = v_isSharedCheck_5930_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5849_);
                    return v___y_5892_;
                }
            }
            7 => {
                v___x_5897_ = lean_st_ref_take(v_a_5852_);
                v_canon_5898_ = crate::leanh::lean_ctor_get(v___x_5897_, 9);
                v_share_5899_ = crate::leanh::lean_ctor_get(v___x_5897_, 0);
                v_maxFVar_5900_ = crate::leanh::lean_ctor_get(v___x_5897_, 1);
                v_proofInstInfo_5901_ = crate::leanh::lean_ctor_get(v___x_5897_, 2);
                v_inferType_5902_ = crate::leanh::lean_ctor_get(v___x_5897_, 3);
                v_getLevel_5903_ = crate::leanh::lean_ctor_get(v___x_5897_, 4);
                v_congrInfo_5904_ = crate::leanh::lean_ctor_get(v___x_5897_, 5);
                v_defEqI_5905_ = crate::leanh::lean_ctor_get(v___x_5897_, 6);
                v_extensions_5906_ = crate::leanh::lean_ctor_get(v___x_5897_, 7);
                v_issues_5907_ = crate::leanh::lean_ctor_get(v___x_5897_, 8);
                v_debug_5908_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5897_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5929_ = (!crate::leanh::lean_is_exclusive(v___x_5897_)) as u8;
                if v_isSharedCheck_5929_ == 0 {
                    v___x_5910_ = v___x_5897_;
                    v_isShared_5911_ = v_isSharedCheck_5929_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5898_);
                    crate::leanh::lean_inc(v_issues_5907_);
                    crate::leanh::lean_inc(v_extensions_5906_);
                    crate::leanh::lean_inc(v_defEqI_5905_);
                    crate::leanh::lean_inc(v_congrInfo_5904_);
                    crate::leanh::lean_inc(v_getLevel_5903_);
                    crate::leanh::lean_inc(v_inferType_5902_);
                    crate::leanh::lean_inc(v_proofInstInfo_5901_);
                    crate::leanh::lean_inc(v_maxFVar_5900_);
                    crate::leanh::lean_inc(v_share_5899_);
                    crate::leanh::lean_dec(v___x_5897_);
                    v___x_5910_ = crate::leanh::lean_box(0);
                    v_isShared_5911_ = v_isSharedCheck_5929_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_cache_5912_ = crate::leanh::lean_ctor_get(v_canon_5898_, 0);
                v_cacheInType_5913_ = crate::leanh::lean_ctor_get(v_canon_5898_, 1);
                v_isSharedCheck_5928_ = (!crate::leanh::lean_is_exclusive(v_canon_5898_)) as u8;
                if v_isSharedCheck_5928_ == 0 {
                    v___x_5915_ = v_canon_5898_;
                    v_isShared_5916_ = v_isSharedCheck_5928_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_5913_);
                    crate::leanh::lean_inc(v_cache_5912_);
                    crate::leanh::lean_dec(v_canon_5898_);
                    v___x_5915_ = crate::leanh::lean_box(0);
                    v_isShared_5916_ = v_isSharedCheck_5928_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc(v_a_5893_);
                v___x_5917_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_5913_, v_e_5849_, v_a_5893_);
                if v_isShared_5916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5915_, 1, v___x_5917_);
                    v___x_5919_ = v___x_5915_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_cache_5912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 1, v___x_5917_);
                    v___x_5919_ = v_reuseFailAlloc_5927_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5910_, 9, v___x_5919_);
                    v___x_5921_ = v___x_5910_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_share_5899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 1, v_maxFVar_5900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 2, v_proofInstInfo_5901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 3, v_inferType_5902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 4, v_getLevel_5903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 5, v_congrInfo_5904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 6, v_defEqI_5905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 7, v_extensions_5906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 8, v_issues_5907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 9, v___x_5919_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5926_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5908_,
                    );
                    v___x_5921_ = v_reuseFailAlloc_5926_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_5922_ = lean_st_ref_set(v_a_5852_, v___x_5921_);
                if v_isShared_5896_ == 0 {
                    v___x_5924_ = v___x_5895_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5893_);
                    v___x_5924_ = v_reuseFailAlloc_5925_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5924_;
            }
            13 => {
                if v_isShared_5938_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5937_, 0);
                    v___x_5940_ = v___x_5937_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_val_5935_);
                    v___x_5940_ = v_reuseFailAlloc_5941_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5940_;
            }
            15 => {
                if v___y_5949_ == 0 {
                    v___x_5950_ = l_Lean_mkAppB(v_g_5846_, v_a_5944_, v___y_5948_);
                    v_a_5859_ = v___x_5950_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_5948_);
                    crate::leanh::lean_dec(v_a_5944_);
                    crate::leanh::lean_dec_ref(v_g_5846_);
                    crate::leanh::lean_inc_ref(v_e_5849_);
                    v_a_5859_ = v_e_5849_;
                    state = 1;
                    continue;
                }
            }
            16 => {
                v___x_5953_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_prop_5847_,
                        v_a_5944_,
                    );
                crate::leanh::lean_dec_ref(v_prop_5847_);
                if v___x_5953_ == 0 {
                    crate::leanh::lean_dec_ref(v_h_5848_);
                    v___y_5948_ = v___y_5952_;
                    v___y_5949_ = v___x_5953_;
                    state = 15;
                    continue;
                } else {
                    v___x_5954_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_h_5848_,
                            v___y_5952_,
                        );
                    crate::leanh::lean_dec_ref(v_h_5848_);
                    v___y_5948_ = v___y_5952_;
                    v___y_5949_ = v___x_5954_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                if v_isShared_5959_ == 0 {
                    v___x_5961_ = v___x_5958_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
                    v___x_5961_ = v_reuseFailAlloc_5962_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5961_;
            }
            19 => {
                if v_isShared_5972_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5971_, 0);
                    v___x_5974_ = v___x_5971_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_val_5969_);
                    v___x_5974_ = v_reuseFailAlloc_5975_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(
    mut v___x_5981_: *mut crate::leanh::LeanObject,
    mut v_a_5982_: *mut crate::leanh::LeanObject,
    mut v___x_5983_: *mut crate::leanh::LeanObject,
    mut v_snd_5984_: *mut crate::leanh::LeanObject,
    mut v___x_5985_: u8,
    mut v_fst_5986_: *mut crate::leanh::LeanObject,
    mut v_____r_5987_: *mut crate::leanh::LeanObject,
    mut v___y_5988_: u8,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_arg_x27_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: u8 = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: u8 = 0;
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6015_: u8 = 0;
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6019_: u8 = 0;
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6023_: u8 = 0;
    let mut v___y_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6035_: u8 = 0;
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6039_: u8 = 0;
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: u8 = 0;
    let mut v_arg_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: u8 = 0;
    let mut v_arg_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6056_: u8 = 0;
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6060_: u8 = 0;
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6066_: u8 = 0;
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6070_: u8 = 0;
    let mut v_a_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6074_: u8 = 0;
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6078_: u8 = 0;
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6088_: u8 = 0;
    let mut v_a_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6092_: u8 = 0;
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___x_5983_);
                v___x_6007_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(
                    v___x_5981_,
                    v_a_5982_,
                    v___x_5983_,
                    v___y_5991_,
                    v___y_5992_,
                    v___y_5993_,
                    v___y_5994_,
                );
                if crate::leanh::lean_obj_tag(v___x_6007_) == 0 {
                    v_a_6008_ = crate::leanh::lean_ctor_get(v___x_6007_, 0);
                    crate::leanh::lean_inc(v_a_6008_);
                    crate::leanh::lean_dec_ref_known(v___x_6007_, 1);
                    v___x_6009_ = (crate::leanh::lean_unbox(v_a_6008_) as u8);
                    crate::leanh::lean_dec(v_a_6008_);
                    match v___x_6009_ {
                        0 => {
                            crate::leanh::lean_inc_ref(v___x_5983_);
                            v___x_6010_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(v___x_5983_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
                            if crate::leanh::lean_obj_tag(v___x_6010_) == 0 {
                                v_a_6011_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                                crate::leanh::lean_inc(v_a_6011_);
                                crate::leanh::lean_dec_ref_known(v___x_6010_, 1);
                                v_arg_x27_5997_ = v_a_6011_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_fst_5986_);
                                crate::leanh::lean_dec(v_snd_5984_);
                                crate::leanh::lean_dec_ref(v___x_5983_);
                                v_a_6012_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                                v_isSharedCheck_6019_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6010_)) as u8;
                                if v_isSharedCheck_6019_ == 0 {
                                    v___x_6014_ = v___x_6010_;
                                    v_isShared_6015_ = v_isSharedCheck_6019_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6012_);
                                    crate::leanh::lean_dec(v___x_6010_);
                                    v___x_6014_ = crate::leanh::lean_box(0);
                                    v_isShared_6015_ = v_isSharedCheck_6019_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            crate::leanh::lean_inc_ref(v___x_5983_);
                            v___x_6020_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                v___x_5983_,
                                v___y_5992_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6020_) == 0 {
                                v_a_6021_ = crate::leanh::lean_ctor_get(v___x_6020_, 0);
                                crate::leanh::lean_inc(v_a_6021_);
                                crate::leanh::lean_dec_ref_known(v___x_6020_, 1);
                                v___x_6040_ = l_Lean_Expr_cleanupAnnotations(v_a_6021_);
                                v___x_6041_ = l_Lean_Expr_isApp(v___x_6040_);
                                if v___x_6041_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_6040_);
                                    v___y_6023_ = v___y_5988_;
                                    v___y_6024_ = v___y_5989_;
                                    v___y_6025_ = v___y_5990_;
                                    v___y_6026_ = v___y_5991_;
                                    v___y_6027_ = v___y_5992_;
                                    v___y_6028_ = v___y_5993_;
                                    v___y_6029_ = v___y_5994_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_arg_6042_ = crate::leanh::lean_ctor_get(v___x_6040_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_6042_);
                                    v___x_6043_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6040_);
                                    v___x_6044_ = l_Lean_Expr_isApp(v___x_6043_);
                                    if v___x_6044_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_6043_);
                                        crate::leanh::lean_dec_ref(v_arg_6042_);
                                        v___y_6023_ = v___y_5988_;
                                        v___y_6024_ = v___y_5989_;
                                        v___y_6025_ = v___y_5990_;
                                        v___y_6026_ = v___y_5991_;
                                        v___y_6027_ = v___y_5992_;
                                        v___y_6028_ = v___y_5993_;
                                        v___y_6029_ = v___y_5994_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_arg_6045_ = crate::leanh::lean_ctor_get(v___x_6043_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_6045_);
                                        v___x_6046_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_6043_);
                                        v___x_6047_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1;
                                        v___x_6048_ =
                                            l_Lean_Expr_isConstOf(v___x_6046_, v___x_6047_);
                                        if v___x_6048_ == 0 {
                                            v___x_6049_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2;
                                            v___x_6050_ =
                                                l_Lean_Expr_isConstOf(v___x_6046_, v___x_6049_);
                                            if v___x_6050_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_6046_);
                                                crate::leanh::lean_dec_ref(v_arg_6045_);
                                                crate::leanh::lean_dec_ref(v_arg_6042_);
                                                v___y_6023_ = v___y_5988_;
                                                v___y_6024_ = v___y_5989_;
                                                v___y_6025_ = v___y_5990_;
                                                v___y_6026_ = v___y_5991_;
                                                v___y_6027_ = v___y_5992_;
                                                v___y_6028_ = v___y_5993_;
                                                v___y_6029_ = v___y_5994_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc_ref(v___x_5983_);
                                                v___x_6051_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_6046_, v_arg_6045_, v_arg_6042_, v___x_5983_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
                                                if crate::leanh::lean_obj_tag(v___x_6051_) == 0 {
                                                    v_a_6052_ =
                                                        crate::leanh::lean_ctor_get(v___x_6051_, 0);
                                                    crate::leanh::lean_inc(v_a_6052_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_6051_,
                                                        1,
                                                    );
                                                    v_arg_x27_5997_ = v_a_6052_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_fst_5986_);
                                                    crate::leanh::lean_dec(v_snd_5984_);
                                                    crate::leanh::lean_dec_ref(v___x_5983_);
                                                    v_a_6053_ =
                                                        crate::leanh::lean_ctor_get(v___x_6051_, 0);
                                                    v_isSharedCheck_6060_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_6051_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_6060_ == 0 {
                                                        v___x_6055_ = v___x_6051_;
                                                        v_isShared_6056_ = v_isSharedCheck_6060_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_6053_);
                                                        crate::leanh::lean_dec(v___x_6051_);
                                                        v___x_6055_ = crate::leanh::lean_box(0);
                                                        v_isShared_6056_ = v_isSharedCheck_6060_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_inc_ref(v___x_5983_);
                                            v___x_6061_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(v___x_6046_, v_arg_6045_, v_arg_6042_, v___x_5983_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
                                            if crate::leanh::lean_obj_tag(v___x_6061_) == 0 {
                                                v_a_6062_ =
                                                    crate::leanh::lean_ctor_get(v___x_6061_, 0);
                                                crate::leanh::lean_inc(v_a_6062_);
                                                crate::leanh::lean_dec_ref_known(v___x_6061_, 1);
                                                v_arg_x27_5997_ = v_a_6062_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_fst_5986_);
                                                crate::leanh::lean_dec(v_snd_5984_);
                                                crate::leanh::lean_dec_ref(v___x_5983_);
                                                v_a_6063_ =
                                                    crate::leanh::lean_ctor_get(v___x_6061_, 0);
                                                v_isSharedCheck_6070_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_6061_))
                                                        as u8;
                                                if v_isSharedCheck_6070_ == 0 {
                                                    v___x_6065_ = v___x_6061_;
                                                    v_isShared_6066_ = v_isSharedCheck_6070_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_6063_);
                                                    crate::leanh::lean_dec(v___x_6061_);
                                                    v___x_6065_ = crate::leanh::lean_box(0);
                                                    v_isShared_6066_ = v_isSharedCheck_6070_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_5986_);
                                crate::leanh::lean_dec(v_snd_5984_);
                                crate::leanh::lean_dec_ref(v___x_5983_);
                                v_a_6071_ = crate::leanh::lean_ctor_get(v___x_6020_, 0);
                                v_isSharedCheck_6078_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6020_)) as u8;
                                if v_isSharedCheck_6078_ == 0 {
                                    v___x_6073_ = v___x_6020_;
                                    v_isShared_6074_ = v_isSharedCheck_6078_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6071_);
                                    crate::leanh::lean_dec(v___x_6020_);
                                    v___x_6073_ = crate::leanh::lean_box(0);
                                    v_isShared_6074_ = v_isSharedCheck_6078_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            crate::leanh::lean_inc_ref(v___x_5983_);
                            v___x_6079_ =
                                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                    v___x_5983_,
                                    v___y_5988_,
                                    v___y_5989_,
                                    v___y_5990_,
                                    v___y_5991_,
                                    v___y_5992_,
                                    v___y_5993_,
                                    v___y_5994_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_6079_) == 0 {
                                v_a_6080_ = crate::leanh::lean_ctor_get(v___x_6079_, 0);
                                crate::leanh::lean_inc(v_a_6080_);
                                crate::leanh::lean_dec_ref_known(v___x_6079_, 1);
                                v_arg_x27_5997_ = v_a_6080_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_fst_5986_);
                                crate::leanh::lean_dec(v_snd_5984_);
                                crate::leanh::lean_dec_ref(v___x_5983_);
                                v_a_6081_ = crate::leanh::lean_ctor_get(v___x_6079_, 0);
                                v_isSharedCheck_6088_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6079_)) as u8;
                                if v_isSharedCheck_6088_ == 0 {
                                    v___x_6083_ = v___x_6079_;
                                    v_isShared_6084_ = v_isSharedCheck_6088_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6081_);
                                    crate::leanh::lean_dec(v___x_6079_);
                                    v___x_6083_ = crate::leanh::lean_box(0);
                                    v_isShared_6084_ = v_isSharedCheck_6088_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_5986_);
                    crate::leanh::lean_dec(v_snd_5984_);
                    crate::leanh::lean_dec_ref(v___x_5983_);
                    v_a_6089_ = crate::leanh::lean_ctor_get(v___x_6007_, 0);
                    v_isSharedCheck_6096_ = (!crate::leanh::lean_is_exclusive(v___x_6007_)) as u8;
                    if v_isSharedCheck_6096_ == 0 {
                        v___x_6091_ = v___x_6007_;
                        v_isShared_6092_ = v_isSharedCheck_6096_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6089_);
                        crate::leanh::lean_dec(v___x_6007_);
                        v___x_6091_ = crate::leanh::lean_box(0);
                        v_isShared_6092_ = v_isSharedCheck_6096_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5998_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_5983_,
                        v_arg_x27_5997_,
                    );
                crate::leanh::lean_dec_ref(v___x_5983_);
                if v___x_5998_ == 0 {
                    crate::leanh::lean_dec(v_fst_5986_);
                    v___x_5999_ = lean_array_fset(v_snd_5984_, v_a_5982_, v_arg_x27_5997_);
                    v___x_6000_ = crate::leanh::lean_box((v___x_5985_) as usize);
                    v___x_6001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6001_, 0, v___x_6000_);
                    crate::leanh::lean_ctor_set(v___x_6001_, 1, v___x_5999_);
                    v___x_6002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6002_, 0, v___x_6001_);
                    v___x_6003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6003_, 0, v___x_6002_);
                    return v___x_6003_;
                } else {
                    crate::leanh::lean_dec_ref(v_arg_x27_5997_);
                    v___x_6004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6004_, 0, v_fst_5986_);
                    crate::leanh::lean_ctor_set(v___x_6004_, 1, v_snd_5984_);
                    v___x_6005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6005_, 0, v___x_6004_);
                    v___x_6006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6006_, 0, v___x_6005_);
                    return v___x_6006_;
                }
            }
            2 => {
                if v_isShared_6015_ == 0 {
                    v___x_6017_ = v___x_6014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
                    v___x_6017_ = v_reuseFailAlloc_6018_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6017_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_5983_);
                v___x_6030_ =
                    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(
                        v___x_5983_,
                        v___x_5985_,
                        v___y_6023_,
                        v___y_6024_,
                        v___y_6025_,
                        v___y_6026_,
                        v___y_6027_,
                        v___y_6028_,
                        v___y_6029_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6030_) == 0 {
                    v_a_6031_ = crate::leanh::lean_ctor_get(v___x_6030_, 0);
                    crate::leanh::lean_inc(v_a_6031_);
                    crate::leanh::lean_dec_ref_known(v___x_6030_, 1);
                    v_arg_x27_5997_ = v_a_6031_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5986_);
                    crate::leanh::lean_dec(v_snd_5984_);
                    crate::leanh::lean_dec_ref(v___x_5983_);
                    v_a_6032_ = crate::leanh::lean_ctor_get(v___x_6030_, 0);
                    v_isSharedCheck_6039_ = (!crate::leanh::lean_is_exclusive(v___x_6030_)) as u8;
                    if v_isSharedCheck_6039_ == 0 {
                        v___x_6034_ = v___x_6030_;
                        v_isShared_6035_ = v_isSharedCheck_6039_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6032_);
                        crate::leanh::lean_dec(v___x_6030_);
                        v___x_6034_ = crate::leanh::lean_box(0);
                        v_isShared_6035_ = v_isSharedCheck_6039_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6035_ == 0 {
                    v___x_6037_ = v___x_6034_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
                    v___x_6037_ = v_reuseFailAlloc_6038_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6037_;
            }
            7 => {
                if v_isShared_6056_ == 0 {
                    v___x_6058_ = v___x_6055_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6053_);
                    v___x_6058_ = v_reuseFailAlloc_6059_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6058_;
            }
            9 => {
                if v_isShared_6066_ == 0 {
                    v___x_6068_ = v___x_6065_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6069_, 0, v_a_6063_);
                    v___x_6068_ = v_reuseFailAlloc_6069_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6068_;
            }
            11 => {
                if v_isShared_6074_ == 0 {
                    v___x_6076_ = v___x_6073_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6071_);
                    v___x_6076_ = v_reuseFailAlloc_6077_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6076_;
            }
            13 => {
                if v_isShared_6084_ == 0 {
                    v___x_6086_ = v___x_6083_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6087_, 0, v_a_6081_);
                    v___x_6086_ = v_reuseFailAlloc_6087_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6086_;
            }
            15 => {
                if v_isShared_6092_ == 0 {
                    v___x_6094_ = v___x_6091_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_a_6089_);
                    v___x_6094_ = v_reuseFailAlloc_6095_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6100_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_;
    v___x_6101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__1;
    v___x_6102_ = l_Lean_Name_append(v___x_6101_, v___x_6100_);
    return v___x_6102_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__3;
    v___x_6105_ = l_Lean_stringToMessageData(v___x_6104_);
    return v___x_6105_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__5;
    v___x_6108_ = l_Lean_stringToMessageData(v___x_6107_);
    return v___x_6108_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__7;
    v___x_6111_ = l_Lean_stringToMessageData(v___x_6110_);
    return v___x_6111_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(
    mut v_upperBound_6112_: *mut crate::leanh::LeanObject,
    mut v___x_6113_: *mut crate::leanh::LeanObject,
    mut v_a_6114_: *mut crate::leanh::LeanObject,
    mut v_b_6115_: *mut crate::leanh::LeanObject,
    mut v___y_6116_: u8,
    mut v___y_6117_: *mut crate::leanh::LeanObject,
    mut v___y_6118_: *mut crate::leanh::LeanObject,
    mut v___y_6119_: *mut crate::leanh::LeanObject,
    mut v___y_6120_: *mut crate::leanh::LeanObject,
    mut v___y_6121_: *mut crate::leanh::LeanObject,
    mut v___y_6122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6129_: u8 = 0;
    let mut v_a_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_a_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6142_: u8 = 0;
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6146_: u8 = 0;
    let mut v___x_6147_: u8 = 0;
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6154_: u8 = 0;
    let mut v_inheritedTraceOptions_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6156_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: u8 = 0;
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6188_: u8 = 0;
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6192_: u8 = 0;
    let mut v_reuseFailAlloc_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: u8 = 0;
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6202_: u8 = 0;
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut v_a_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6210_: u8 = 0;
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6214_: u8 = 0;
    let mut v_isSharedCheck_6215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6147_ = lean_nat_dec_lt(v_a_6114_, v_upperBound_6112_);
                if v___x_6147_ == 0 {
                    crate::leanh::lean_dec(v_a_6114_);
                    v___x_6148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6148_, 0, v_b_6115_);
                    return v___x_6148_;
                } else {
                    v_options_6149_ = crate::leanh::lean_ctor_get(v___y_6121_, 2);
                    v_fst_6150_ = crate::leanh::lean_ctor_get(v_b_6115_, 0);
                    v_snd_6151_ = crate::leanh::lean_ctor_get(v_b_6115_, 1);
                    v_isSharedCheck_6215_ = (!crate::leanh::lean_is_exclusive(v_b_6115_)) as u8;
                    if v_isSharedCheck_6215_ == 0 {
                        v___x_6153_ = v_b_6115_;
                        v_isShared_6154_ = v_isSharedCheck_6215_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6151_);
                        crate::leanh::lean_inc(v_fst_6150_);
                        crate::leanh::lean_dec(v_b_6115_);
                        v___x_6153_ = crate::leanh::lean_box(0);
                        v_isShared_6154_ = v_isSharedCheck_6215_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6125_) == 0 {
                    v_a_6126_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    v_isSharedCheck_6138_ = (!crate::leanh::lean_is_exclusive(v___y_6125_)) as u8;
                    if v_isSharedCheck_6138_ == 0 {
                        v___x_6128_ = v___y_6125_;
                        v_isShared_6129_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6126_);
                        crate::leanh::lean_dec(v___y_6125_);
                        v___x_6128_ = crate::leanh::lean_box(0);
                        v_isShared_6129_ = v_isSharedCheck_6138_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6114_);
                    v_a_6139_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    v_isSharedCheck_6146_ = (!crate::leanh::lean_is_exclusive(v___y_6125_)) as u8;
                    if v_isSharedCheck_6146_ == 0 {
                        v___x_6141_ = v___y_6125_;
                        v_isShared_6142_ = v_isSharedCheck_6146_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6139_);
                        crate::leanh::lean_dec(v___y_6125_);
                        v___x_6141_ = crate::leanh::lean_box(0);
                        v_isShared_6142_ = v_isSharedCheck_6146_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6126_) == 0 {
                    crate::leanh::lean_dec(v_a_6114_);
                    v_a_6130_ = crate::leanh::lean_ctor_get(v_a_6126_, 0);
                    crate::leanh::lean_inc(v_a_6130_);
                    crate::leanh::lean_dec_ref_known(v_a_6126_, 1);
                    if v_isShared_6129_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6128_, 0, v_a_6130_);
                        v___x_6132_ = v___x_6128_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_a_6130_);
                        v___x_6132_ = v_reuseFailAlloc_6133_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6128_);
                    v_a_6134_ = crate::leanh::lean_ctor_get(v_a_6126_, 0);
                    crate::leanh::lean_inc(v_a_6134_);
                    crate::leanh::lean_dec_ref_known(v_a_6126_, 1);
                    v___x_6135_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6136_ = lean_nat_add(v_a_6114_, v___x_6135_);
                    crate::leanh::lean_dec(v_a_6114_);
                    v_a_6114_ = v___x_6136_;
                    v_b_6115_ = v_a_6134_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_6132_;
            }
            4 => {
                if v_isShared_6142_ == 0 {
                    v___x_6144_ = v___x_6141_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6139_);
                    v___x_6144_ = v_reuseFailAlloc_6145_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6144_;
            }
            6 => {
                v_inheritedTraceOptions_6155_ = crate::leanh::lean_ctor_get(v___y_6121_, 13);
                v_hasTrace_6156_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6149_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_6157_ = lean_array_fget(v_snd_6151_, v_a_6114_);
                if v_hasTrace_6156_ == 0 {
                    crate::leanh::lean_del_object(v___x_6153_);
                    state = 7;
                    continue;
                } else {
                    v___x_6161_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn___closed__3_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_;
                    v___x_6162_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__2);
                    v___x_6163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6155_,
                        v_options_6149_,
                        v___x_6162_,
                    );
                    if v___x_6163_ == 0 {
                        crate::leanh::lean_del_object(v___x_6153_);
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_6157_);
                        v___x_6164_ =
                            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(
                                v___x_6113_,
                                v_a_6114_,
                                v___x_6157_,
                                v___y_6119_,
                                v___y_6120_,
                                v___y_6121_,
                                v___y_6122_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6164_) == 0 {
                            v_a_6165_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                            crate::leanh::lean_inc(v_a_6165_);
                            crate::leanh::lean_dec_ref_known(v___x_6164_, 1);
                            crate::leanh::lean_inc(v___y_6122_);
                            crate::leanh::lean_inc_ref(v___y_6121_);
                            crate::leanh::lean_inc(v___y_6120_);
                            crate::leanh::lean_inc_ref(v___y_6119_);
                            crate::leanh::lean_inc(v___x_6157_);
                            v___x_6166_ = lean_infer_type(
                                v___x_6157_,
                                v___y_6119_,
                                v___y_6120_,
                                v___y_6121_,
                                v___y_6122_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6166_) == 0 {
                                v_a_6167_ = crate::leanh::lean_ctor_get(v___x_6166_, 0);
                                crate::leanh::lean_inc(v_a_6167_);
                                crate::leanh::lean_dec_ref_known(v___x_6166_, 1);
                                v___x_6168_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__4);
                                v___x_6194_ = (crate::leanh::lean_unbox(v_a_6165_) as u8);
                                crate::leanh::lean_dec(v_a_6165_);
                                match v___x_6194_ {
                                    0 => {
                                        v___x_6195_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__1;
                                        v___y_6170_ = v___x_6195_;
                                        state = 8;
                                        continue;
                                    }
                                    1 => {
                                        v___x_6196_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__3;
                                        v___y_6170_ = v___x_6196_;
                                        state = 8;
                                        continue;
                                    }
                                    2 => {
                                        v___x_6197_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__5;
                                        v___y_6170_ = v___x_6197_;
                                        state = 8;
                                        continue;
                                    }
                                    _ => {
                                        v___x_6198_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instReprShouldCanonResult___lam__0___closed__7;
                                        v___y_6170_ = v___x_6198_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6165_);
                                crate::leanh::lean_dec(v___x_6157_);
                                crate::leanh::lean_del_object(v___x_6153_);
                                crate::leanh::lean_dec(v_snd_6151_);
                                crate::leanh::lean_dec(v_fst_6150_);
                                crate::leanh::lean_dec(v_a_6114_);
                                v_a_6199_ = crate::leanh::lean_ctor_get(v___x_6166_, 0);
                                v_isSharedCheck_6206_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6166_)) as u8;
                                if v_isSharedCheck_6206_ == 0 {
                                    v___x_6201_ = v___x_6166_;
                                    v_isShared_6202_ = v_isSharedCheck_6206_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6199_);
                                    crate::leanh::lean_dec(v___x_6166_);
                                    v___x_6201_ = crate::leanh::lean_box(0);
                                    v_isShared_6202_ = v_isSharedCheck_6206_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6157_);
                            crate::leanh::lean_del_object(v___x_6153_);
                            crate::leanh::lean_dec(v_snd_6151_);
                            crate::leanh::lean_dec(v_fst_6150_);
                            crate::leanh::lean_dec(v_a_6114_);
                            v_a_6207_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                            v_isSharedCheck_6214_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6164_)) as u8;
                            if v_isSharedCheck_6214_ == 0 {
                                v___x_6209_ = v___x_6164_;
                                v_isShared_6210_ = v_isSharedCheck_6214_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6207_);
                                crate::leanh::lean_dec(v___x_6164_);
                                v___x_6209_ = crate::leanh::lean_box(0);
                                v_isShared_6210_ = v_isSharedCheck_6214_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                v___x_6159_ = crate::leanh::lean_box(0);
                v___x_6160_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_6113_, v_a_6114_, v___x_6157_, v_snd_6151_, v___x_6147_, v_fst_6150_, v___x_6159_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                v___y_6125_ = v___x_6160_;
                state = 1;
                continue;
            }
            8 => {
                crate::leanh::lean_inc(v___y_6170_);
                v___x_6171_ = l_Lean_MessageData_ofFormat(v___y_6170_);
                if v_isShared_6154_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6153_, 7);
                    crate::leanh::lean_ctor_set(v___x_6153_, 1, v___x_6171_);
                    crate::leanh::lean_ctor_set(v___x_6153_, 0, v___x_6168_);
                    v___x_6173_ = v___x_6153_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6193_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 1, v___x_6171_);
                    v___x_6173_ = v_reuseFailAlloc_6193_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6174_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__6);
                v___x_6175_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6175_, 0, v___x_6173_);
                crate::leanh::lean_ctor_set(v___x_6175_, 1, v___x_6174_);
                crate::leanh::lean_inc(v___x_6157_);
                v___x_6176_ = l_Lean_MessageData_ofExpr(v___x_6157_);
                v___x_6177_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6177_, 0, v___x_6175_);
                crate::leanh::lean_ctor_set(v___x_6177_, 1, v___x_6176_);
                v___x_6178_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___closed__8);
                v___x_6179_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6179_, 0, v___x_6177_);
                crate::leanh::lean_ctor_set(v___x_6179_, 1, v___x_6178_);
                v___x_6180_ = l_Lean_MessageData_ofExpr(v_a_6167_);
                v___x_6181_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6181_, 0, v___x_6179_);
                crate::leanh::lean_ctor_set(v___x_6181_, 1, v___x_6180_);
                v___x_6182_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v___x_6161_, v___x_6181_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                if crate::leanh::lean_obj_tag(v___x_6182_) == 0 {
                    v_a_6183_ = crate::leanh::lean_ctor_get(v___x_6182_, 0);
                    crate::leanh::lean_inc(v_a_6183_);
                    crate::leanh::lean_dec_ref_known(v___x_6182_, 1);
                    v___x_6184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_6113_, v_a_6114_, v___x_6157_, v_snd_6151_, v___x_6147_, v_fst_6150_, v_a_6183_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
                    v___y_6125_ = v___x_6184_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6157_);
                    crate::leanh::lean_dec(v_snd_6151_);
                    crate::leanh::lean_dec(v_fst_6150_);
                    crate::leanh::lean_dec(v_a_6114_);
                    v_a_6185_ = crate::leanh::lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6192_ = (!crate::leanh::lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6192_ == 0 {
                        v___x_6187_ = v___x_6182_;
                        v_isShared_6188_ = v_isSharedCheck_6192_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6185_);
                        crate::leanh::lean_dec(v___x_6182_);
                        v___x_6187_ = crate::leanh::lean_box(0);
                        v_isShared_6188_ = v_isSharedCheck_6192_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_6188_ == 0 {
                    v___x_6190_ = v___x_6187_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6191_, 0, v_a_6185_);
                    v___x_6190_ = v_reuseFailAlloc_6191_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6190_;
            }
            12 => {
                if v_isShared_6202_ == 0 {
                    v___x_6204_ = v___x_6201_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6205_, 0, v_a_6199_);
                    v___x_6204_ = v_reuseFailAlloc_6205_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6204_;
            }
            14 => {
                if v_isShared_6210_ == 0 {
                    v___x_6212_ = v___x_6209_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6213_, 0, v_a_6207_);
                    v___x_6212_ = v_reuseFailAlloc_6213_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(
    mut v_e_6216_: *mut crate::leanh::LeanObject,
    mut v_x_6217_: *mut crate::leanh::LeanObject,
    mut v_x_6218_: *mut crate::leanh::LeanObject,
    mut v_x_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: u8,
    mut v___y_6221_: *mut crate::leanh::LeanObject,
    mut v___y_6222_: *mut crate::leanh::LeanObject,
    mut v___y_6223_: *mut crate::leanh::LeanObject,
    mut v___y_6224_: *mut crate::leanh::LeanObject,
    mut v___y_6225_: *mut crate::leanh::LeanObject,
    mut v___y_6226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_6230_: u8 = 0;
    let mut v_f_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6232_: u8 = 0;
    let mut v___y_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6245_: u8 = 0;
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v_fst_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: u8 = 0;
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut v_a_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6270_: u8 = 0;
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6274_: u8 = 0;
    let mut v_reuseFailAlloc_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6276_: u8 = 0;
    let mut v_unused_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6281_: u8 = 0;
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6285_: u8 = 0;
    let mut v_args_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_6288_: u8 = 0;
    let mut v___y_6289_: u8 = 0;
    let mut v___y_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: u8 = 0;
    let mut v___x_6299_: u8 = 0;
    let mut v___y_6301_: u8 = 0;
    let mut v___y_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_6308_: u8 = 0;
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_6310_: u8 = 0;
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6317_: u8 = 0;
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6321_: u8 = 0;
    let mut v_fn_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: u8 = 0;
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: u8 = 0;
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: u8 = 0;
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prop_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6348_: u8 = 0;
    let mut v___x_6349_: u8 = 0;
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6217_) == 5 {
                    v_fn_6322_ = crate::leanh::lean_ctor_get(v_x_6217_, 0);
                    crate::leanh::lean_inc_ref(v_fn_6322_);
                    v_arg_6323_ = crate::leanh::lean_ctor_get(v_x_6217_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6323_);
                    crate::leanh::lean_dec_ref_known(v_x_6217_, 2);
                    v___x_6324_ = lean_array_set(v_x_6218_, v_x_6219_, v_arg_6323_);
                    v___x_6325_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6326_ = lean_nat_sub(v_x_6219_, v___x_6325_);
                    crate::leanh::lean_dec(v_x_6219_);
                    v_x_6217_ = v_fn_6322_;
                    v_x_6218_ = v___x_6324_;
                    v_x_6219_ = v___x_6326_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_6219_);
                    v___x_6328_ = lean_array_get_size(v_x_6218_);
                    v___x_6329_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_6330_ = lean_nat_dec_eq(v___x_6328_, v___x_6329_);
                    if v___x_6330_ == 0 {
                        v___y_6301_ = v___y_6220_;
                        v___y_6302_ = v___y_6221_;
                        v___y_6303_ = v___y_6222_;
                        v___y_6304_ = v___y_6223_;
                        v___y_6305_ = v___y_6224_;
                        v___y_6306_ = v___y_6225_;
                        v___y_6307_ = v___y_6226_;
                        state = 12;
                        continue;
                    } else {
                        v___x_6331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___closed__1;
                        v___x_6332_ = l_Lean_Expr_isConstOf(v_x_6217_, v___x_6331_);
                        if v___x_6332_ == 0 {
                            v___x_6333_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2;
                            v___x_6334_ = l_Lean_Expr_isConstOf(v_x_6217_, v___x_6333_);
                            if v___x_6334_ == 0 {
                                v___y_6301_ = v___y_6220_;
                                v___y_6302_ = v___y_6221_;
                                v___y_6303_ = v___y_6222_;
                                v___y_6304_ = v___y_6223_;
                                v___y_6305_ = v___y_6224_;
                                v___y_6306_ = v___y_6225_;
                                v___y_6307_ = v___y_6226_;
                                state = 12;
                                continue;
                            } else {
                                v___x_6335_ = l_Lean_instInhabitedExpr;
                                v___x_6336_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6337_ = lean_array_get(v___x_6335_, v_x_6218_, v___x_6336_);
                                v___x_6338_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_6339_ = lean_array_get(v___x_6335_, v_x_6218_, v___x_6338_);
                                crate::leanh::lean_dec_ref(v_x_6218_);
                                v___x_6340_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(v_x_6217_, v___x_6337_, v___x_6339_, v_e_6216_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_);
                                return v___x_6340_;
                            }
                        } else {
                            v___x_6341_ = l_Lean_instInhabitedExpr;
                            v___x_6342_ = crate::leanh::lean_unsigned_to_nat(0);
                            v_prop_6343_ =
                                lean_array_get_borrowed(v___x_6341_, v_x_6218_, v___x_6342_);
                            crate::leanh::lean_inc(v_prop_6343_);
                            v___x_6344_ =
                                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                    v_prop_6343_,
                                    v___y_6220_,
                                    v___y_6221_,
                                    v___y_6222_,
                                    v___y_6223_,
                                    v___y_6224_,
                                    v___y_6225_,
                                    v___y_6226_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_6344_) == 0 {
                                v_a_6345_ = crate::leanh::lean_ctor_get(v___x_6344_, 0);
                                v_isSharedCheck_6359_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6344_)) as u8;
                                if v_isSharedCheck_6359_ == 0 {
                                    v___x_6347_ = v___x_6344_;
                                    v_isShared_6348_ = v_isSharedCheck_6359_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6345_);
                                    crate::leanh::lean_dec(v___x_6344_);
                                    v___x_6347_ = crate::leanh::lean_box(0);
                                    v_isShared_6348_ = v_isSharedCheck_6359_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_x_6218_);
                                crate::leanh::lean_dec_ref(v_x_6217_);
                                crate::leanh::lean_dec_ref(v_e_6216_);
                                return v___x_6344_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6239_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_f_6231_);
                v___x_6240_ = l_Lean_Meta_getFunInfo(
                    v_f_6231_,
                    v___x_6239_,
                    v___y_6235_,
                    v___y_6236_,
                    v___y_6237_,
                    v___y_6238_,
                );
                if crate::leanh::lean_obj_tag(v___x_6240_) == 0 {
                    v_a_6241_ = crate::leanh::lean_ctor_get(v___x_6240_, 0);
                    crate::leanh::lean_inc(v_a_6241_);
                    crate::leanh::lean_dec_ref_known(v___x_6240_, 1);
                    v_paramInfo_6242_ = crate::leanh::lean_ctor_get(v_a_6241_, 0);
                    v_isSharedCheck_6276_ = (!crate::leanh::lean_is_exclusive(v_a_6241_)) as u8;
                    if v_isSharedCheck_6276_ == 0 {
                        v_unused_6277_ = crate::leanh::lean_ctor_get(v_a_6241_, 1);
                        crate::leanh::lean_dec(v_unused_6277_);
                        v___x_6244_ = v_a_6241_;
                        v_isShared_6245_ = v_isSharedCheck_6276_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_paramInfo_6242_);
                        crate::leanh::lean_dec(v_a_6241_);
                        v___x_6244_ = crate::leanh::lean_box(0);
                        v_isShared_6245_ = v_isSharedCheck_6276_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6231_);
                    crate::leanh::lean_dec_ref(v___y_6229_);
                    crate::leanh::lean_dec_ref(v_e_6216_);
                    v_a_6278_ = crate::leanh::lean_ctor_get(v___x_6240_, 0);
                    v_isSharedCheck_6285_ = (!crate::leanh::lean_is_exclusive(v___x_6240_)) as u8;
                    if v_isSharedCheck_6285_ == 0 {
                        v___x_6280_ = v___x_6240_;
                        v_isShared_6281_ = v_isSharedCheck_6285_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6278_);
                        crate::leanh::lean_dec(v___x_6240_);
                        v___x_6280_ = crate::leanh::lean_box(0);
                        v_isShared_6281_ = v_isSharedCheck_6285_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6246_ = lean_array_get_size(v___y_6229_);
                v___x_6247_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6248_ = crate::leanh::lean_box((v_modified_6230_) as usize);
                if v_isShared_6245_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6244_, 1, v___y_6229_);
                    crate::leanh::lean_ctor_set(v___x_6244_, 0, v___x_6248_);
                    v___x_6250_ = v___x_6244_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 0, v___x_6248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6275_, 1, v___y_6229_);
                    v___x_6250_ = v_reuseFailAlloc_6275_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v___x_6246_, v_paramInfo_6242_, v___x_6247_, v___x_6250_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
                crate::leanh::lean_dec_ref(v_paramInfo_6242_);
                if crate::leanh::lean_obj_tag(v___x_6251_) == 0 {
                    v_a_6252_ = crate::leanh::lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6266_ = (!crate::leanh::lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6266_ == 0 {
                        v___x_6254_ = v___x_6251_;
                        v_isShared_6255_ = v_isSharedCheck_6266_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6252_);
                        crate::leanh::lean_dec(v___x_6251_);
                        v___x_6254_ = crate::leanh::lean_box(0);
                        v_isShared_6255_ = v_isSharedCheck_6266_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6231_);
                    crate::leanh::lean_dec_ref(v_e_6216_);
                    v_a_6267_ = crate::leanh::lean_ctor_get(v___x_6251_, 0);
                    v_isSharedCheck_6274_ = (!crate::leanh::lean_is_exclusive(v___x_6251_)) as u8;
                    if v_isSharedCheck_6274_ == 0 {
                        v___x_6269_ = v___x_6251_;
                        v_isShared_6270_ = v_isSharedCheck_6274_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6267_);
                        crate::leanh::lean_dec(v___x_6251_);
                        v___x_6269_ = crate::leanh::lean_box(0);
                        v_isShared_6270_ = v_isSharedCheck_6274_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_6256_ = crate::leanh::lean_ctor_get(v_a_6252_, 0);
                v___x_6257_ = (crate::leanh::lean_unbox(v_fst_6256_) as u8);
                if v___x_6257_ == 0 {
                    crate::leanh::lean_dec(v_a_6252_);
                    crate::leanh::lean_dec_ref(v_f_6231_);
                    if v_isShared_6255_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6254_, 0, v_e_6216_);
                        v___x_6259_ = v___x_6254_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_e_6216_);
                        v___x_6259_ = v_reuseFailAlloc_6260_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6216_);
                    v_snd_6261_ = crate::leanh::lean_ctor_get(v_a_6252_, 1);
                    crate::leanh::lean_inc(v_snd_6261_);
                    crate::leanh::lean_dec(v_a_6252_);
                    v___x_6262_ = l_Lean_mkAppN(v_f_6231_, v_snd_6261_);
                    crate::leanh::lean_dec(v_snd_6261_);
                    if v_isShared_6255_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6254_, 0, v___x_6262_);
                        v___x_6264_ = v___x_6254_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6265_, 0, v___x_6262_);
                        v___x_6264_ = v_reuseFailAlloc_6265_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_6259_;
            }
            6 => {
                return v___x_6264_;
            }
            7 => {
                if v_isShared_6270_ == 0 {
                    v___x_6272_ = v___x_6269_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6267_);
                    v___x_6272_ = v_reuseFailAlloc_6273_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6272_;
            }
            9 => {
                if v_isShared_6281_ == 0 {
                    v___x_6283_ = v___x_6280_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6284_, 0, v_a_6278_);
                    v___x_6283_ = v_reuseFailAlloc_6284_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6283_;
            }
            11 => {
                crate::leanh::lean_inc_ref(v_x_6217_);
                v___x_6296_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                    v_x_6217_,
                    v___y_6289_,
                    v___y_6290_,
                    v___y_6291_,
                    v___y_6292_,
                    v___y_6293_,
                    v___y_6294_,
                    v___y_6295_,
                );
                if crate::leanh::lean_obj_tag(v___x_6296_) == 0 {
                    v_a_6297_ = crate::leanh::lean_ctor_get(v___x_6296_, 0);
                    crate::leanh::lean_inc(v_a_6297_);
                    crate::leanh::lean_dec_ref_known(v___x_6296_, 1);
                    v___x_6298_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_6217_, v_a_6297_,
                        );
                    if v___x_6298_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_6217_);
                        v___x_6299_ = 1;
                        v___y_6229_ = v_args_6287_;
                        v_modified_6230_ = v___x_6299_;
                        v_f_6231_ = v_a_6297_;
                        v___y_6232_ = v___y_6289_;
                        v___y_6233_ = v___y_6290_;
                        v___y_6234_ = v___y_6291_;
                        v___y_6235_ = v___y_6292_;
                        v___y_6236_ = v___y_6293_;
                        v___y_6237_ = v___y_6294_;
                        v___y_6238_ = v___y_6295_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6297_);
                        v___y_6229_ = v_args_6287_;
                        v_modified_6230_ = v_modified_6288_;
                        v_f_6231_ = v_x_6217_;
                        v___y_6232_ = v___y_6289_;
                        v___y_6233_ = v___y_6290_;
                        v___y_6234_ = v___y_6291_;
                        v___y_6235_ = v___y_6292_;
                        v___y_6236_ = v___y_6293_;
                        v___y_6237_ = v___y_6294_;
                        v___y_6238_ = v___y_6295_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_6287_);
                    crate::leanh::lean_dec_ref(v_x_6217_);
                    crate::leanh::lean_dec_ref(v_e_6216_);
                    return v___x_6296_;
                }
            }
            12 => {
                v_modified_6308_ = 0;
                v___x_6309_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f___closed__6;
                v_modified_6310_ = l_Lean_Expr_isConstOf(v_x_6217_, v___x_6309_);
                if v_modified_6310_ == 0 {
                    v_args_6287_ = v_x_6218_;
                    v_modified_6288_ = v_modified_6308_;
                    v___y_6289_ = v___y_6301_;
                    v___y_6290_ = v___y_6302_;
                    v___y_6291_ = v___y_6303_;
                    v___y_6292_ = v___y_6304_;
                    v___y_6293_ = v___y_6305_;
                    v___y_6294_ = v___y_6306_;
                    v___y_6295_ = v___y_6307_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_x_6218_);
                    v___x_6311_ =
                        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_normOfNatArgs_x3f(
                            v_x_6218_,
                            v___y_6304_,
                            v___y_6305_,
                            v___y_6306_,
                            v___y_6307_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6311_) == 0 {
                        v_a_6312_ = crate::leanh::lean_ctor_get(v___x_6311_, 0);
                        crate::leanh::lean_inc(v_a_6312_);
                        crate::leanh::lean_dec_ref_known(v___x_6311_, 1);
                        if crate::leanh::lean_obj_tag(v_a_6312_) == 1 {
                            crate::leanh::lean_dec_ref(v_x_6218_);
                            v_val_6313_ = crate::leanh::lean_ctor_get(v_a_6312_, 0);
                            crate::leanh::lean_inc(v_val_6313_);
                            crate::leanh::lean_dec_ref_known(v_a_6312_, 1);
                            v_args_6287_ = v_val_6313_;
                            v_modified_6288_ = v_modified_6310_;
                            v___y_6289_ = v___y_6301_;
                            v___y_6290_ = v___y_6302_;
                            v___y_6291_ = v___y_6303_;
                            v___y_6292_ = v___y_6304_;
                            v___y_6293_ = v___y_6305_;
                            v___y_6294_ = v___y_6306_;
                            v___y_6295_ = v___y_6307_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6312_);
                            v_args_6287_ = v_x_6218_;
                            v_modified_6288_ = v_modified_6308_;
                            v___y_6289_ = v___y_6301_;
                            v___y_6290_ = v___y_6302_;
                            v___y_6291_ = v___y_6303_;
                            v___y_6292_ = v___y_6304_;
                            v___y_6293_ = v___y_6305_;
                            v___y_6294_ = v___y_6306_;
                            v___y_6295_ = v___y_6307_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_6218_);
                        crate::leanh::lean_dec_ref(v_x_6217_);
                        crate::leanh::lean_dec_ref(v_e_6216_);
                        v_a_6314_ = crate::leanh::lean_ctor_get(v___x_6311_, 0);
                        v_isSharedCheck_6321_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6311_)) as u8;
                        if v_isSharedCheck_6321_ == 0 {
                            v___x_6316_ = v___x_6311_;
                            v_isShared_6317_ = v_isSharedCheck_6321_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6314_);
                            crate::leanh::lean_dec(v___x_6311_);
                            v___x_6316_ = crate::leanh::lean_box(0);
                            v_isShared_6317_ = v_isSharedCheck_6321_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if v_isShared_6317_ == 0 {
                    v___x_6319_ = v___x_6316_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6320_, 0, v_a_6314_);
                    v___x_6319_ = v_reuseFailAlloc_6320_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6319_;
            }
            15 => {
                v___x_6349_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_prop_6343_,
                        v_a_6345_,
                    );
                if v___x_6349_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_6216_);
                    v___x_6350_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6351_ = lean_array_get(v___x_6341_, v_x_6218_, v___x_6350_);
                    crate::leanh::lean_dec_ref(v_x_6218_);
                    v___x_6352_ = l_Lean_mkAppB(v_x_6217_, v_a_6345_, v___x_6351_);
                    if v_isShared_6348_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6347_, 0, v___x_6352_);
                        v___x_6354_ = v___x_6347_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6355_, 0, v___x_6352_);
                        v___x_6354_ = v_reuseFailAlloc_6355_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6345_);
                    crate::leanh::lean_dec_ref(v_x_6218_);
                    crate::leanh::lean_dec_ref(v_x_6217_);
                    if v_isShared_6348_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6347_, 0, v_e_6216_);
                        v___x_6357_ = v___x_6347_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_6358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6358_, 0, v_e_6216_);
                        v___x_6357_ = v_reuseFailAlloc_6358_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_6354_;
            }
            17 => {
                return v___x_6357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(
    mut v_e_6360_: *mut crate::leanh::LeanObject,
    mut v_a_6361_: u8,
    mut v_a_6362_: *mut crate::leanh::LeanObject,
    mut v_a_6363_: *mut crate::leanh::LeanObject,
    mut v_a_6364_: *mut crate::leanh::LeanObject,
    mut v_a_6365_: *mut crate::leanh::LeanObject,
    mut v_a_6366_: *mut crate::leanh::LeanObject,
    mut v_a_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_6369_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_reduceProjFn_x3f___redArg___closed__0);
    v_nargs_6370_ = l_Lean_Expr_getAppNumArgs(v_e_6360_);
    crate::leanh::lean_inc(v_nargs_6370_);
    v___x_6371_ = lean_mk_array(v_nargs_6370_, v_dummy_6369_);
    v___x_6372_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_6373_ = lean_nat_sub(v_nargs_6370_, v___x_6372_);
    crate::leanh::lean_dec(v_nargs_6370_);
    crate::leanh::lean_inc_ref(v_e_6360_);
    v___x_6374_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_6360_, v_e_6360_, v___x_6371_, v___x_6373_, v_a_6361_, v_a_6362_, v_a_6363_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_);
    return v___x_6374_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(
    mut v_e_6375_: *mut crate::leanh::LeanObject,
    mut v_a_6376_: u8,
    mut v_a_6377_: *mut crate::leanh::LeanObject,
    mut v_a_6378_: *mut crate::leanh::LeanObject,
    mut v_a_6379_: *mut crate::leanh::LeanObject,
    mut v_a_6380_: *mut crate::leanh::LeanObject,
    mut v_a_6381_: *mut crate::leanh::LeanObject,
    mut v_a_6382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6384_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(
        v_e_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_,
    );
    if crate::leanh::lean_obj_tag(v___x_6384_) == 0 {
        let mut v_a_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6385_ = crate::leanh::lean_ctor_get(v___x_6384_, 0);
        crate::leanh::lean_inc(v_a_6385_);
        crate::leanh::lean_dec_ref_known(v___x_6384_, 1);
        v___x_6386_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_postReduce(
            v_a_6385_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_,
        );
        return v___x_6386_;
    } else {
        return v___x_6384_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(
    mut v_e_6387_: *mut crate::leanh::LeanObject,
    mut v_a_6388_: u8,
    mut v_a_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_a_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
    mut v_a_6393_: *mut crate::leanh::LeanObject,
    mut v_a_6394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6406_: u8 = 0;
    let mut v_val_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6412_: u8 = 0;
    let mut v_a_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6416_: u8 = 0;
    let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6420_: u8 = 0;
    let mut v_a_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6424_: u8 = 0;
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6396_ = l_Lean_Meta_reduceMatcher_x3f(
                    v_e_6387_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_,
                );
                if crate::leanh::lean_obj_tag(v___x_6396_) == 0 {
                    v_a_6397_ = crate::leanh::lean_ctor_get(v___x_6396_, 0);
                    crate::leanh::lean_inc(v_a_6397_);
                    crate::leanh::lean_dec_ref_known(v___x_6396_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6397_) == 0 {
                        crate::leanh::lean_dec_ref(v_e_6387_);
                        v_val_6398_ = crate::leanh::lean_ctor_get(v_a_6397_, 0);
                        crate::leanh::lean_inc_ref(v_val_6398_);
                        crate::leanh::lean_dec_ref_known(v_a_6397_, 1);
                        v___x_6399_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                            v_val_6398_,
                            v_a_6388_,
                            v_a_6389_,
                            v_a_6390_,
                            v_a_6391_,
                            v_a_6392_,
                            v_a_6393_,
                            v_a_6394_,
                        );
                        return v___x_6399_;
                    } else {
                        crate::leanh::lean_dec(v_a_6397_);
                        v___x_6400_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(v_e_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_);
                        if crate::leanh::lean_obj_tag(v___x_6400_) == 0 {
                            v_a_6401_ = crate::leanh::lean_ctor_get(v___x_6400_, 0);
                            crate::leanh::lean_inc(v_a_6401_);
                            crate::leanh::lean_dec_ref_known(v___x_6400_, 1);
                            v___x_6402_ = l_Lean_Meta_reduceMatcher_x3f(
                                v_a_6401_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6402_) == 0 {
                                v_a_6403_ = crate::leanh::lean_ctor_get(v___x_6402_, 0);
                                v_isSharedCheck_6412_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6402_)) as u8;
                                if v_isSharedCheck_6412_ == 0 {
                                    v___x_6405_ = v___x_6402_;
                                    v_isShared_6406_ = v_isSharedCheck_6412_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6403_);
                                    crate::leanh::lean_dec(v___x_6402_);
                                    v___x_6405_ = crate::leanh::lean_box(0);
                                    v_isShared_6406_ = v_isSharedCheck_6412_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6401_);
                                v_a_6413_ = crate::leanh::lean_ctor_get(v___x_6402_, 0);
                                v_isSharedCheck_6420_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6402_)) as u8;
                                if v_isSharedCheck_6420_ == 0 {
                                    v___x_6415_ = v___x_6402_;
                                    v_isShared_6416_ = v_isSharedCheck_6420_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6413_);
                                    crate::leanh::lean_dec(v___x_6402_);
                                    v___x_6415_ = crate::leanh::lean_box(0);
                                    v_isShared_6416_ = v_isSharedCheck_6420_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_6400_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6387_);
                    v_a_6421_ = crate::leanh::lean_ctor_get(v___x_6396_, 0);
                    v_isSharedCheck_6428_ = (!crate::leanh::lean_is_exclusive(v___x_6396_)) as u8;
                    if v_isSharedCheck_6428_ == 0 {
                        v___x_6423_ = v___x_6396_;
                        v_isShared_6424_ = v_isSharedCheck_6428_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6421_);
                        crate::leanh::lean_dec(v___x_6396_);
                        v___x_6423_ = crate::leanh::lean_box(0);
                        v_isShared_6424_ = v_isSharedCheck_6428_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6403_) == 0 {
                    crate::leanh::lean_del_object(v___x_6405_);
                    crate::leanh::lean_dec(v_a_6401_);
                    v_val_6407_ = crate::leanh::lean_ctor_get(v_a_6403_, 0);
                    crate::leanh::lean_inc_ref(v_val_6407_);
                    crate::leanh::lean_dec_ref_known(v_a_6403_, 1);
                    v___x_6408_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                        v_val_6407_,
                        v_a_6388_,
                        v_a_6389_,
                        v_a_6390_,
                        v_a_6391_,
                        v_a_6392_,
                        v_a_6393_,
                        v_a_6394_,
                    );
                    return v___x_6408_;
                } else {
                    crate::leanh::lean_dec(v_a_6403_);
                    if v_isShared_6406_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6405_, 0, v_a_6401_);
                        v___x_6410_ = v___x_6405_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_a_6401_);
                        v___x_6410_ = v_reuseFailAlloc_6411_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6410_;
            }
            3 => {
                if v_isShared_6416_ == 0 {
                    v___x_6418_ = v___x_6415_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_a_6413_);
                    v___x_6418_ = v_reuseFailAlloc_6419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6418_;
            }
            5 => {
                if v_isShared_6424_ == 0 {
                    v___x_6426_ = v___x_6423_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6427_, 0, v_a_6421_);
                    v___x_6426_ = v_reuseFailAlloc_6427_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(
    mut v_e_6435_: *mut crate::leanh::LeanObject,
    mut v_a_6436_: u8,
    mut v_a_6437_: *mut crate::leanh::LeanObject,
    mut v_a_6438_: *mut crate::leanh::LeanObject,
    mut v_a_6439_: *mut crate::leanh::LeanObject,
    mut v_a_6440_: *mut crate::leanh::LeanObject,
    mut v_a_6441_: *mut crate::leanh::LeanObject,
    mut v_a_6442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6447_: u8 = 0;
    let mut v___y_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: u8 = 0;
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: u8 = 0;
    let mut v_arg_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: u8 = 0;
    let mut v_arg_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: u8 = 0;
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_6435_);
                v___x_6444_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6435_, v_a_6440_);
                if crate::leanh::lean_obj_tag(v___x_6444_) == 0 {
                    v_a_6445_ = crate::leanh::lean_ctor_get(v___x_6444_, 0);
                    crate::leanh::lean_inc(v_a_6445_);
                    crate::leanh::lean_dec_ref_known(v___x_6444_, 1);
                    v___x_6456_ = l_Lean_Expr_cleanupAnnotations(v_a_6445_);
                    v___x_6457_ = l_Lean_Expr_isApp(v___x_6456_);
                    if v___x_6457_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_6456_);
                        v___y_6447_ = v_a_6436_;
                        v___y_6448_ = v_a_6437_;
                        v___y_6449_ = v_a_6438_;
                        v___y_6450_ = v_a_6439_;
                        v___y_6451_ = v_a_6440_;
                        v___y_6452_ = v_a_6441_;
                        v___y_6453_ = v_a_6442_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_6458_ = crate::leanh::lean_ctor_get(v___x_6456_, 1);
                        crate::leanh::lean_inc_ref(v_arg_6458_);
                        v___x_6459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6456_);
                        v___x_6460_ = l_Lean_Expr_isApp(v___x_6459_);
                        if v___x_6460_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6459_);
                            crate::leanh::lean_dec_ref(v_arg_6458_);
                            v___y_6447_ = v_a_6436_;
                            v___y_6448_ = v_a_6437_;
                            v___y_6449_ = v_a_6438_;
                            v___y_6450_ = v_a_6439_;
                            v___y_6451_ = v_a_6440_;
                            v___y_6452_ = v_a_6441_;
                            v___y_6453_ = v_a_6442_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_6461_ = crate::leanh::lean_ctor_get(v___x_6459_, 1);
                            crate::leanh::lean_inc_ref(v_arg_6461_);
                            v___x_6462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6459_);
                            v___x_6463_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___closed__2;
                            v___x_6464_ = l_Lean_Expr_isConstOf(v___x_6462_, v___x_6463_);
                            if v___x_6464_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_6462_);
                                crate::leanh::lean_dec_ref(v_arg_6461_);
                                crate::leanh::lean_dec_ref(v_arg_6458_);
                                v___y_6447_ = v_a_6436_;
                                v___y_6448_ = v_a_6437_;
                                v___y_6449_ = v_a_6438_;
                                v___y_6450_ = v_a_6439_;
                                v___y_6451_ = v_a_6440_;
                                v___y_6452_ = v_a_6441_;
                                v___y_6453_ = v_a_6442_;
                                state = 1;
                                continue;
                            } else {
                                v___x_6465_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(v___x_6462_, v_arg_6461_, v_arg_6458_, v_e_6435_, v_a_6436_, v_a_6437_, v_a_6438_, v_a_6439_, v_a_6440_, v_a_6441_, v_a_6442_);
                                return v___x_6465_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6435_);
                    return v___x_6444_;
                }
            }
            1 => {
                v___x_6454_ = 0;
                v___x_6455_ =
                    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(
                        v_e_6435_,
                        v___x_6454_,
                        v___y_6447_,
                        v___y_6448_,
                        v___y_6449_,
                        v___y_6450_,
                        v___y_6451_,
                        v___y_6452_,
                        v___y_6453_,
                    );
                return v___x_6455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(
    mut v_f_6466_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6467_: *mut crate::leanh::LeanObject,
    mut v_c_6468_: *mut crate::leanh::LeanObject,
    mut v_inst_6469_: *mut crate::leanh::LeanObject,
    mut v_a_6470_: *mut crate::leanh::LeanObject,
    mut v_b_6471_: *mut crate::leanh::LeanObject,
    mut v_a_6472_: u8,
    mut v_a_6473_: *mut crate::leanh::LeanObject,
    mut v_a_6474_: *mut crate::leanh::LeanObject,
    mut v_a_6475_: *mut crate::leanh::LeanObject,
    mut v_a_6476_: *mut crate::leanh::LeanObject,
    mut v_a_6477_: *mut crate::leanh::LeanObject,
    mut v_a_6478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: u8 = 0;
    let mut v___x_6483_: u8 = 0;
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6494_: u8 = 0;
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6499_: u8 = 0;
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6480_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                    v_c_6468_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_, v_a_6477_,
                    v_a_6478_,
                );
                if crate::leanh::lean_obj_tag(v___x_6480_) == 0 {
                    v_a_6481_ = crate::leanh::lean_ctor_get(v___x_6480_, 0);
                    crate::leanh::lean_inc_n(v_a_6481_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6480_, 1);
                    v___x_6482_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isTrueCond(
                        v_a_6481_,
                    );
                    if v___x_6482_ == 0 {
                        crate::leanh::lean_inc(v_a_6481_);
                        v___x_6483_ =
                            l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_isFalseCond(
                                v_a_6481_,
                            );
                        if v___x_6483_ == 0 {
                            v___x_6484_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_6467_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_);
                            if crate::leanh::lean_obj_tag(v___x_6484_) == 0 {
                                v_a_6485_ = crate::leanh::lean_ctor_get(v___x_6484_, 0);
                                crate::leanh::lean_inc(v_a_6485_);
                                crate::leanh::lean_dec_ref_known(v___x_6484_, 1);
                                v___x_6486_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(v_inst_6469_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_);
                                if crate::leanh::lean_obj_tag(v___x_6486_) == 0 {
                                    v_a_6487_ = crate::leanh::lean_ctor_get(v___x_6486_, 0);
                                    crate::leanh::lean_inc(v_a_6487_);
                                    crate::leanh::lean_dec_ref_known(v___x_6486_, 1);
                                    v___x_6488_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_a_6470_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_);
                                    if crate::leanh::lean_obj_tag(v___x_6488_) == 0 {
                                        v_a_6489_ = crate::leanh::lean_ctor_get(v___x_6488_, 0);
                                        crate::leanh::lean_inc(v_a_6489_);
                                        crate::leanh::lean_dec_ref_known(v___x_6488_, 1);
                                        v___x_6490_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_6471_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_, v_a_6477_, v_a_6478_);
                                        if crate::leanh::lean_obj_tag(v___x_6490_) == 0 {
                                            v_a_6491_ = crate::leanh::lean_ctor_get(v___x_6490_, 0);
                                            v_isSharedCheck_6499_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6490_))
                                                    as u8;
                                            if v_isSharedCheck_6499_ == 0 {
                                                v___x_6493_ = v___x_6490_;
                                                v_isShared_6494_ = v_isSharedCheck_6499_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6491_);
                                                crate::leanh::lean_dec(v___x_6490_);
                                                v___x_6493_ = crate::leanh::lean_box(0);
                                                v_isShared_6494_ = v_isSharedCheck_6499_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_6489_);
                                            crate::leanh::lean_dec(v_a_6487_);
                                            crate::leanh::lean_dec(v_a_6485_);
                                            crate::leanh::lean_dec(v_a_6481_);
                                            crate::leanh::lean_dec_ref(v_f_6466_);
                                            return v___x_6490_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6487_);
                                        crate::leanh::lean_dec(v_a_6485_);
                                        crate::leanh::lean_dec(v_a_6481_);
                                        crate::leanh::lean_dec_ref(v_b_6471_);
                                        crate::leanh::lean_dec_ref(v_f_6466_);
                                        return v___x_6488_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6485_);
                                    crate::leanh::lean_dec(v_a_6481_);
                                    crate::leanh::lean_dec_ref(v_b_6471_);
                                    crate::leanh::lean_dec_ref(v_a_6470_);
                                    crate::leanh::lean_dec_ref(v_f_6466_);
                                    return v___x_6486_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6481_);
                                crate::leanh::lean_dec_ref(v_b_6471_);
                                crate::leanh::lean_dec_ref(v_a_6470_);
                                crate::leanh::lean_dec_ref(v_inst_6469_);
                                crate::leanh::lean_dec_ref(v_f_6466_);
                                return v___x_6484_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6481_);
                            crate::leanh::lean_dec_ref(v_a_6470_);
                            crate::leanh::lean_dec_ref(v_inst_6469_);
                            crate::leanh::lean_dec_ref(v_00_u03b1_6467_);
                            crate::leanh::lean_dec_ref(v_f_6466_);
                            v___x_6500_ =
                                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                    v_b_6471_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_,
                                    v_a_6476_, v_a_6477_, v_a_6478_,
                                );
                            return v___x_6500_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6481_);
                        crate::leanh::lean_dec_ref(v_b_6471_);
                        crate::leanh::lean_dec_ref(v_inst_6469_);
                        crate::leanh::lean_dec_ref(v_00_u03b1_6467_);
                        crate::leanh::lean_dec_ref(v_f_6466_);
                        v___x_6501_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                            v_a_6470_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_, v_a_6476_,
                            v_a_6477_, v_a_6478_,
                        );
                        return v___x_6501_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_6471_);
                    crate::leanh::lean_dec_ref(v_a_6470_);
                    crate::leanh::lean_dec_ref(v_inst_6469_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_6467_);
                    crate::leanh::lean_dec_ref(v_f_6466_);
                    return v___x_6480_;
                }
            }
            1 => {
                v___x_6495_ = l_Lean_mkApp5(
                    v_f_6466_, v_a_6485_, v_a_6481_, v_a_6487_, v_a_6489_, v_a_6491_,
                );
                if v_isShared_6494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6493_, 0, v___x_6495_);
                    v___x_6497_ = v___x_6493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6498_, 0, v___x_6495_);
                    v___x_6497_ = v_reuseFailAlloc_6498_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6497_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(
    mut v_f_6502_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6503_: *mut crate::leanh::LeanObject,
    mut v_c_6504_: *mut crate::leanh::LeanObject,
    mut v_a_6505_: *mut crate::leanh::LeanObject,
    mut v_b_6506_: *mut crate::leanh::LeanObject,
    mut v_a_6507_: u8,
    mut v_a_6508_: *mut crate::leanh::LeanObject,
    mut v_a_6509_: *mut crate::leanh::LeanObject,
    mut v_a_6510_: *mut crate::leanh::LeanObject,
    mut v_a_6511_: *mut crate::leanh::LeanObject,
    mut v_a_6512_: *mut crate::leanh::LeanObject,
    mut v_a_6513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: u8 = 0;
    let mut v___x_6518_: u8 = 0;
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6527_: u8 = 0;
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6532_: u8 = 0;
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6515_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                    v_c_6504_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_, v_a_6512_,
                    v_a_6513_,
                );
                if crate::leanh::lean_obj_tag(v___x_6515_) == 0 {
                    v_a_6516_ = crate::leanh::lean_ctor_get(v___x_6515_, 0);
                    crate::leanh::lean_inc_n(v_a_6516_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6515_, 1);
                    v___x_6517_ = l_Lean_Expr_isBoolTrue(v_a_6516_);
                    if v___x_6517_ == 0 {
                        crate::leanh::lean_inc(v_a_6516_);
                        v___x_6518_ = l_Lean_Expr_isBoolFalse(v_a_6516_);
                        if v___x_6518_ == 0 {
                            v___x_6519_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(v_00_u03b1_6503_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
                            if crate::leanh::lean_obj_tag(v___x_6519_) == 0 {
                                v_a_6520_ = crate::leanh::lean_ctor_get(v___x_6519_, 0);
                                crate::leanh::lean_inc(v_a_6520_);
                                crate::leanh::lean_dec_ref_known(v___x_6519_, 1);
                                v___x_6521_ =
                                    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                        v_a_6505_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_,
                                        v_a_6511_, v_a_6512_, v_a_6513_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_6521_) == 0 {
                                    v_a_6522_ = crate::leanh::lean_ctor_get(v___x_6521_, 0);
                                    crate::leanh::lean_inc(v_a_6522_);
                                    crate::leanh::lean_dec_ref_known(v___x_6521_, 1);
                                    v___x_6523_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(v_b_6506_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
                                    if crate::leanh::lean_obj_tag(v___x_6523_) == 0 {
                                        v_a_6524_ = crate::leanh::lean_ctor_get(v___x_6523_, 0);
                                        v_isSharedCheck_6532_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6523_)) as u8;
                                        if v_isSharedCheck_6532_ == 0 {
                                            v___x_6526_ = v___x_6523_;
                                            v_isShared_6527_ = v_isSharedCheck_6532_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6524_);
                                            crate::leanh::lean_dec(v___x_6523_);
                                            v___x_6526_ = crate::leanh::lean_box(0);
                                            v_isShared_6527_ = v_isSharedCheck_6532_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6522_);
                                        crate::leanh::lean_dec(v_a_6520_);
                                        crate::leanh::lean_dec(v_a_6516_);
                                        crate::leanh::lean_dec_ref(v_f_6502_);
                                        return v___x_6523_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6520_);
                                    crate::leanh::lean_dec(v_a_6516_);
                                    crate::leanh::lean_dec_ref(v_b_6506_);
                                    crate::leanh::lean_dec_ref(v_f_6502_);
                                    return v___x_6521_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6516_);
                                crate::leanh::lean_dec_ref(v_b_6506_);
                                crate::leanh::lean_dec_ref(v_a_6505_);
                                crate::leanh::lean_dec_ref(v_f_6502_);
                                return v___x_6519_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6516_);
                            crate::leanh::lean_dec_ref(v_a_6505_);
                            crate::leanh::lean_dec_ref(v_00_u03b1_6503_);
                            crate::leanh::lean_dec_ref(v_f_6502_);
                            v___x_6533_ =
                                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                    v_b_6506_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_,
                                    v_a_6511_, v_a_6512_, v_a_6513_,
                                );
                            return v___x_6533_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6516_);
                        crate::leanh::lean_dec_ref(v_b_6506_);
                        crate::leanh::lean_dec_ref(v_00_u03b1_6503_);
                        crate::leanh::lean_dec_ref(v_f_6502_);
                        v___x_6534_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                            v_a_6505_, v_a_6507_, v_a_6508_, v_a_6509_, v_a_6510_, v_a_6511_,
                            v_a_6512_, v_a_6513_,
                        );
                        return v___x_6534_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_6506_);
                    crate::leanh::lean_dec_ref(v_a_6505_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_6503_);
                    crate::leanh::lean_dec_ref(v_f_6502_);
                    return v___x_6515_;
                }
            }
            1 => {
                v___x_6528_ = l_Lean_mkApp4(v_f_6502_, v_a_6520_, v_a_6516_, v_a_6522_, v_a_6524_);
                if v_isShared_6527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6526_, 0, v___x_6528_);
                    v___x_6530_ = v___x_6526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6531_, 0, v___x_6528_);
                    v___x_6530_ = v_reuseFailAlloc_6531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(
    mut v_e_6535_: *mut crate::leanh::LeanObject,
    mut v_a_6536_: u8,
    mut v_a_6537_: *mut crate::leanh::LeanObject,
    mut v_a_6538_: *mut crate::leanh::LeanObject,
    mut v_a_6539_: *mut crate::leanh::LeanObject,
    mut v_a_6540_: *mut crate::leanh::LeanObject,
    mut v_a_6541_: *mut crate::leanh::LeanObject,
    mut v_a_6542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6547_: u8 = 0;
    let mut v___y_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: u8 = 0;
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6564_: u8 = 0;
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6568_: u8 = 0;
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: u8 = 0;
    let mut v_arg_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: u8 = 0;
    let mut v_arg_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: u8 = 0;
    let mut v_arg_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v_arg_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: u8 = 0;
    let mut v_arg_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: u8 = 0;
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_6535_);
                v___x_6544_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6535_, v_a_6540_);
                if crate::leanh::lean_obj_tag(v___x_6544_) == 0 {
                    v_a_6545_ = crate::leanh::lean_ctor_get(v___x_6544_, 0);
                    crate::leanh::lean_inc(v_a_6545_);
                    crate::leanh::lean_dec_ref_known(v___x_6544_, 1);
                    v___x_6570_ = l_Lean_Expr_cleanupAnnotations(v_a_6545_);
                    v___x_6571_ = l_Lean_Expr_isApp(v___x_6570_);
                    if v___x_6571_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_6570_);
                        v___y_6547_ = v_a_6536_;
                        v___y_6548_ = v_a_6537_;
                        v___y_6549_ = v_a_6538_;
                        v___y_6550_ = v_a_6539_;
                        v___y_6551_ = v_a_6540_;
                        v___y_6552_ = v_a_6541_;
                        v___y_6553_ = v_a_6542_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_6572_ = crate::leanh::lean_ctor_get(v___x_6570_, 1);
                        crate::leanh::lean_inc_ref(v_arg_6572_);
                        v___x_6573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6570_);
                        v___x_6574_ = l_Lean_Expr_isApp(v___x_6573_);
                        if v___x_6574_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6573_);
                            crate::leanh::lean_dec_ref(v_arg_6572_);
                            v___y_6547_ = v_a_6536_;
                            v___y_6548_ = v_a_6537_;
                            v___y_6549_ = v_a_6538_;
                            v___y_6550_ = v_a_6539_;
                            v___y_6551_ = v_a_6540_;
                            v___y_6552_ = v_a_6541_;
                            v___y_6553_ = v_a_6542_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_6575_ = crate::leanh::lean_ctor_get(v___x_6573_, 1);
                            crate::leanh::lean_inc_ref(v_arg_6575_);
                            v___x_6576_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6573_);
                            v___x_6577_ = l_Lean_Expr_isApp(v___x_6576_);
                            if v___x_6577_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_6576_);
                                crate::leanh::lean_dec_ref(v_arg_6575_);
                                crate::leanh::lean_dec_ref(v_arg_6572_);
                                v___y_6547_ = v_a_6536_;
                                v___y_6548_ = v_a_6537_;
                                v___y_6549_ = v_a_6538_;
                                v___y_6550_ = v_a_6539_;
                                v___y_6551_ = v_a_6540_;
                                v___y_6552_ = v_a_6541_;
                                v___y_6553_ = v_a_6542_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_6578_ = crate::leanh::lean_ctor_get(v___x_6576_, 1);
                                crate::leanh::lean_inc_ref(v_arg_6578_);
                                v___x_6579_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6576_);
                                v___x_6580_ = l_Lean_Expr_isApp(v___x_6579_);
                                if v___x_6580_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_6579_);
                                    crate::leanh::lean_dec_ref(v_arg_6578_);
                                    crate::leanh::lean_dec_ref(v_arg_6575_);
                                    crate::leanh::lean_dec_ref(v_arg_6572_);
                                    v___y_6547_ = v_a_6536_;
                                    v___y_6548_ = v_a_6537_;
                                    v___y_6549_ = v_a_6538_;
                                    v___y_6550_ = v_a_6539_;
                                    v___y_6551_ = v_a_6540_;
                                    v___y_6552_ = v_a_6541_;
                                    v___y_6553_ = v_a_6542_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_6581_ = crate::leanh::lean_ctor_get(v___x_6579_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_6581_);
                                    v___x_6582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6579_);
                                    v___x_6583_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__1;
                                    v___x_6584_ = l_Lean_Expr_isConstOf(v___x_6582_, v___x_6583_);
                                    if v___x_6584_ == 0 {
                                        v___x_6585_ = l_Lean_Expr_isApp(v___x_6582_);
                                        if v___x_6585_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_6582_);
                                            crate::leanh::lean_dec_ref(v_arg_6581_);
                                            crate::leanh::lean_dec_ref(v_arg_6578_);
                                            crate::leanh::lean_dec_ref(v_arg_6575_);
                                            crate::leanh::lean_dec_ref(v_arg_6572_);
                                            v___y_6547_ = v_a_6536_;
                                            v___y_6548_ = v_a_6537_;
                                            v___y_6549_ = v_a_6538_;
                                            v___y_6550_ = v_a_6539_;
                                            v___y_6551_ = v_a_6540_;
                                            v___y_6552_ = v_a_6541_;
                                            v___y_6553_ = v_a_6542_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_6586_ =
                                                crate::leanh::lean_ctor_get(v___x_6582_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_6586_);
                                            v___x_6587_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_6582_);
                                            v___x_6588_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___closed__3;
                                            v___x_6589_ =
                                                l_Lean_Expr_isConstOf(v___x_6587_, v___x_6588_);
                                            if v___x_6589_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_6587_);
                                                crate::leanh::lean_dec_ref(v_arg_6586_);
                                                crate::leanh::lean_dec_ref(v_arg_6581_);
                                                crate::leanh::lean_dec_ref(v_arg_6578_);
                                                crate::leanh::lean_dec_ref(v_arg_6575_);
                                                crate::leanh::lean_dec_ref(v_arg_6572_);
                                                v___y_6547_ = v_a_6536_;
                                                v___y_6548_ = v_a_6537_;
                                                v___y_6549_ = v_a_6538_;
                                                v___y_6550_ = v_a_6539_;
                                                v___y_6551_ = v_a_6540_;
                                                v___y_6552_ = v_a_6541_;
                                                v___y_6553_ = v_a_6542_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_6535_);
                                                v___x_6590_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(v___x_6587_, v_arg_6586_, v_arg_6581_, v_arg_6578_, v_arg_6575_, v_arg_6572_, v_a_6536_, v_a_6537_, v_a_6538_, v_a_6539_, v_a_6540_, v_a_6541_, v_a_6542_);
                                                return v___x_6590_;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_6535_);
                                        v___x_6591_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(v___x_6582_, v_arg_6581_, v_arg_6578_, v_arg_6575_, v_arg_6572_, v_a_6536_, v_a_6537_, v_a_6538_, v_a_6539_, v_a_6540_, v_a_6541_, v_a_6542_);
                                        return v___x_6591_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6535_);
                    return v___x_6544_;
                }
            }
            1 => {
                v___x_6554_ = l_Lean_Expr_getAppFn(v_e_6535_);
                if crate::leanh::lean_obj_tag(v___x_6554_) == 4 {
                    v_declName_6555_ = crate::leanh::lean_ctor_get(v___x_6554_, 0);
                    crate::leanh::lean_inc(v_declName_6555_);
                    crate::leanh::lean_dec_ref_known(v___x_6554_, 2);
                    v___x_6556_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_6555_, v___y_6553_);
                    if crate::leanh::lean_obj_tag(v___x_6556_) == 0 {
                        v_a_6557_ = crate::leanh::lean_ctor_get(v___x_6556_, 0);
                        crate::leanh::lean_inc(v_a_6557_);
                        crate::leanh::lean_dec_ref_known(v___x_6556_, 1);
                        v___x_6558_ = (crate::leanh::lean_unbox(v_a_6557_) as u8);
                        crate::leanh::lean_dec(v_a_6557_);
                        if v___x_6558_ == 0 {
                            v___x_6559_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_6535_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_);
                            return v___x_6559_;
                        } else {
                            v___x_6560_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(v_e_6535_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_);
                            return v___x_6560_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6535_);
                        v_a_6561_ = crate::leanh::lean_ctor_get(v___x_6556_, 0);
                        v_isSharedCheck_6568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6556_)) as u8;
                        if v_isSharedCheck_6568_ == 0 {
                            v___x_6563_ = v___x_6556_;
                            v_isShared_6564_ = v_isSharedCheck_6568_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6561_);
                            crate::leanh::lean_dec(v___x_6556_);
                            v___x_6563_ = crate::leanh::lean_box(0);
                            v_isShared_6564_ = v_isSharedCheck_6568_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_6554_);
                    v___x_6569_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(v_e_6535_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_);
                    return v___x_6569_;
                }
            }
            2 => {
                if v_isShared_6564_ == 0 {
                    v___x_6566_ = v___x_6563_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6567_, 0, v_a_6561_);
                    v___x_6566_ = v_reuseFailAlloc_6567_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6595_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__2;
    v___x_6596_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_6597_ = crate::leanh::lean_unsigned_to_nat(1887);
    v___x_6598_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__1;
    v___x_6599_ =
        l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__0;
    v___x_6600_ = l_mkPanicMessageWithDecl(
        v___x_6599_,
        v___x_6598_,
        v___x_6597_,
        v___x_6596_,
        v___x_6595_,
    );
    return v___x_6600_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(
    mut v_e_6601_: *mut crate::leanh::LeanObject,
    mut v_a_6602_: u8,
    mut v_a_6603_: *mut crate::leanh::LeanObject,
    mut v_a_6604_: *mut crate::leanh::LeanObject,
    mut v_a_6605_: *mut crate::leanh::LeanObject,
    mut v_a_6606_: *mut crate::leanh::LeanObject,
    mut v_a_6607_: *mut crate::leanh::LeanObject,
    mut v_a_6608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6619_: u8 = 0;
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut v_a_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6635_: u8 = 0;
    let mut v_typeName_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: usize = 0;
    let mut v___x_6640_: usize = 0;
    let mut v___x_6641_: u8 = 0;
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6610_ = l_Lean_Expr_projExpr_x21(v_e_6601_);
                v___x_6611_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                    v___x_6610_,
                    v_a_6602_,
                    v_a_6603_,
                    v_a_6604_,
                    v_a_6605_,
                    v_a_6606_,
                    v_a_6607_,
                    v_a_6608_,
                );
                if crate::leanh::lean_obj_tag(v___x_6611_) == 0 {
                    v_a_6612_ = crate::leanh::lean_ctor_get(v___x_6611_, 0);
                    crate::leanh::lean_inc(v_a_6612_);
                    crate::leanh::lean_dec_ref_known(v___x_6611_, 1);
                    if crate::leanh::lean_obj_tag(v_e_6601_) == 11 {
                        v_typeName_6636_ = crate::leanh::lean_ctor_get(v_e_6601_, 0);
                        v_idx_6637_ = crate::leanh::lean_ctor_get(v_e_6601_, 1);
                        v_struct_6638_ = crate::leanh::lean_ctor_get(v_e_6601_, 2);
                        v___x_6639_ = lean_ptr_addr(v_struct_6638_);
                        v___x_6640_ = lean_ptr_addr(v_a_6612_);
                        v___x_6641_ = lean_usize_dec_eq(v___x_6639_, v___x_6640_);
                        if v___x_6641_ == 0 {
                            crate::leanh::lean_inc(v_idx_6637_);
                            crate::leanh::lean_inc(v_typeName_6636_);
                            crate::leanh::lean_dec_ref_known(v_e_6601_, 3);
                            v___x_6642_ = l_Lean_Expr_proj___override(
                                v_typeName_6636_,
                                v_idx_6637_,
                                v_a_6612_,
                            );
                            v___y_6614_ = v___x_6642_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6612_);
                            v___y_6614_ = v_e_6601_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6612_);
                        crate::leanh::lean_dec_ref(v_e_6601_);
                        v___x_6643_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3_once), _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___closed__3);
                        v___x_6644_ = l_panic___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj_spec__4(v___x_6643_);
                        v___y_6614_ = v___x_6644_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6601_);
                    return v___x_6611_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_6614_);
                v___x_6615_ = l_Lean_Meta_reduceProj_x3f(
                    v___y_6614_,
                    v_a_6605_,
                    v_a_6606_,
                    v_a_6607_,
                    v_a_6608_,
                );
                if crate::leanh::lean_obj_tag(v___x_6615_) == 0 {
                    v_a_6616_ = crate::leanh::lean_ctor_get(v___x_6615_, 0);
                    v_isSharedCheck_6627_ = (!crate::leanh::lean_is_exclusive(v___x_6615_)) as u8;
                    if v_isSharedCheck_6627_ == 0 {
                        v___x_6618_ = v___x_6615_;
                        v_isShared_6619_ = v_isSharedCheck_6627_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6616_);
                        crate::leanh::lean_dec(v___x_6615_);
                        v___x_6618_ = crate::leanh::lean_box(0);
                        v_isShared_6619_ = v_isSharedCheck_6627_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6614_);
                    v_a_6628_ = crate::leanh::lean_ctor_get(v___x_6615_, 0);
                    v_isSharedCheck_6635_ = (!crate::leanh::lean_is_exclusive(v___x_6615_)) as u8;
                    if v_isSharedCheck_6635_ == 0 {
                        v___x_6630_ = v___x_6615_;
                        v_isShared_6631_ = v_isSharedCheck_6635_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6628_);
                        crate::leanh::lean_dec(v___x_6615_);
                        v___x_6630_ = crate::leanh::lean_box(0);
                        v_isShared_6631_ = v_isSharedCheck_6635_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6616_) == 0 {
                    if v_isShared_6619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6618_, 0, v___y_6614_);
                        v___x_6621_ = v___x_6618_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6622_, 0, v___y_6614_);
                        v___x_6621_ = v_reuseFailAlloc_6622_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6614_);
                    v_val_6623_ = crate::leanh::lean_ctor_get(v_a_6616_, 0);
                    crate::leanh::lean_inc(v_val_6623_);
                    crate::leanh::lean_dec_ref_known(v_a_6616_, 1);
                    if v_isShared_6619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6618_, 0, v_val_6623_);
                        v___x_6625_ = v___x_6618_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_val_6623_);
                        v___x_6625_ = v_reuseFailAlloc_6626_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6621_;
            }
            4 => {
                return v___x_6625_;
            }
            5 => {
                if v_isShared_6631_ == 0 {
                    v___x_6633_ = v___x_6630_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6634_, 0, v_a_6628_);
                    v___x_6633_ = v_reuseFailAlloc_6634_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
    mut v_e_6645_: *mut crate::leanh::LeanObject,
    mut v_a_6646_: u8,
    mut v_a_6647_: *mut crate::leanh::LeanObject,
    mut v_a_6648_: *mut crate::leanh::LeanObject,
    mut v_a_6649_: *mut crate::leanh::LeanObject,
    mut v_a_6650_: *mut crate::leanh::LeanObject,
    mut v_a_6651_: *mut crate::leanh::LeanObject,
    mut v_a_6652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6662_: u8 = 0;
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6666_: u8 = 0;
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6671_: u8 = 0;
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6683_: u8 = 0;
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v_cache_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6691_: u8 = 0;
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6703_: u8 = 0;
    let mut v_isSharedCheck_6704_: u8 = 0;
    let mut v_isSharedCheck_6705_: u8 = 0;
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6713_: u8 = 0;
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6722_: u8 = 0;
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6734_: u8 = 0;
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6737_: u8 = 0;
    let mut v_cache_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6742_: u8 = 0;
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6754_: u8 = 0;
    let mut v_isSharedCheck_6755_: u8 = 0;
    let mut v_isSharedCheck_6756_: u8 = 0;
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6773_: u8 = 0;
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6785_: u8 = 0;
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6788_: u8 = 0;
    let mut v_cache_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6793_: u8 = 0;
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6805_: u8 = 0;
    let mut v_isSharedCheck_6806_: u8 = 0;
    let mut v_isSharedCheck_6807_: u8 = 0;
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6815_: u8 = 0;
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6819_: u8 = 0;
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6824_: u8 = 0;
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6836_: u8 = 0;
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6839_: u8 = 0;
    let mut v_cache_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6844_: u8 = 0;
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6856_: u8 = 0;
    let mut v_isSharedCheck_6857_: u8 = 0;
    let mut v_isSharedCheck_6858_: u8 = 0;
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6867_: u8 = 0;
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6871_: u8 = 0;
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6876_: u8 = 0;
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6888_: u8 = 0;
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6891_: u8 = 0;
    let mut v_cache_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6896_: u8 = 0;
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6908_: u8 = 0;
    let mut v_isSharedCheck_6909_: u8 = 0;
    let mut v_isSharedCheck_6910_: u8 = 0;
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6922_: u8 = 0;
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6927_: u8 = 0;
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6939_: u8 = 0;
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6942_: u8 = 0;
    let mut v_cache_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6947_: u8 = 0;
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6959_: u8 = 0;
    let mut v_isSharedCheck_6960_: u8 = 0;
    let mut v_isSharedCheck_6961_: u8 = 0;
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6969_: u8 = 0;
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6973_: u8 = 0;
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6978_: u8 = 0;
    let mut v___x_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_6990_: u8 = 0;
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6993_: u8 = 0;
    let mut v_cache_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6998_: u8 = 0;
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v_isSharedCheck_7011_: u8 = 0;
    let mut v_isSharedCheck_7012_: u8 = 0;
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7020_: u8 = 0;
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7024_: u8 = 0;
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7029_: u8 = 0;
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_7041_: u8 = 0;
    let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7044_: u8 = 0;
    let mut v_cache_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7049_: u8 = 0;
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7061_: u8 = 0;
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v_isSharedCheck_7063_: u8 = 0;
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7071_: u8 = 0;
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7075_: u8 = 0;
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7080_: u8 = 0;
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_7092_: u8 = 0;
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7095_: u8 = 0;
    let mut v_cache_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7100_: u8 = 0;
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7112_: u8 = 0;
    let mut v_isSharedCheck_7113_: u8 = 0;
    let mut v_isSharedCheck_7114_: u8 = 0;
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7122_: u8 = 0;
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7126_: u8 = 0;
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7131_: u8 = 0;
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_7143_: u8 = 0;
    let mut v___x_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7146_: u8 = 0;
    let mut v_cache_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheInType_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7151_: u8 = 0;
    let mut v___x_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7163_: u8 = 0;
    let mut v_isSharedCheck_7164_: u8 = 0;
    let mut v_isSharedCheck_7165_: u8 = 0;
    let mut v_data_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7172_: u8 = 0;
    let mut v___x_7173_: usize = 0;
    let mut v___x_7174_: usize = 0;
    let mut v___x_7175_: u8 = 0;
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7183_: u8 = 0;
    let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_6645_) {
                7 => {
                    v___x_6654_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0;
                    if v_a_6646_ == 0 {
                        v___x_6655_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6656_ = crate::leanh::lean_ctor_get(v___x_6655_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6656_);
                        crate::leanh::lean_dec(v___x_6655_);
                        v_cache_6657_ = crate::leanh::lean_ctor_get(v_canon_6656_, 0);
                        crate::leanh::lean_inc_ref(v_cache_6657_);
                        crate::leanh::lean_dec_ref(v_canon_6656_);
                        v___x_6658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_6657_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cache_6657_);
                        if crate::leanh::lean_obj_tag(v___x_6658_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                            v_val_6659_ = crate::leanh::lean_ctor_get(v___x_6658_, 0);
                            v_isSharedCheck_6666_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6658_)) as u8;
                            if v_isSharedCheck_6666_ == 0 {
                                v___x_6661_ = v___x_6658_;
                                v_isShared_6662_ = v_isSharedCheck_6666_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6659_);
                                crate::leanh::lean_dec(v___x_6658_);
                                v___x_6661_ = crate::leanh::lean_box(0);
                                v_isShared_6662_ = v_isSharedCheck_6666_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6658_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6667_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_6654_, v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6667_) == 0 {
                                v_a_6668_ = crate::leanh::lean_ctor_get(v___x_6667_, 0);
                                v_isSharedCheck_6705_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6667_)) as u8;
                                if v_isSharedCheck_6705_ == 0 {
                                    v___x_6670_ = v___x_6667_;
                                    v_isShared_6671_ = v_isSharedCheck_6705_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6668_);
                                    crate::leanh::lean_dec(v___x_6667_);
                                    v___x_6670_ = crate::leanh::lean_box(0);
                                    v_isShared_6671_ = v_isSharedCheck_6705_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                                return v___x_6667_;
                            }
                        }
                    } else {
                        v___x_6706_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6707_ = crate::leanh::lean_ctor_get(v___x_6706_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6707_);
                        crate::leanh::lean_dec(v___x_6706_);
                        v_cacheInType_6708_ = crate::leanh::lean_ctor_get(v_canon_6707_, 1);
                        crate::leanh::lean_inc_ref(v_cacheInType_6708_);
                        crate::leanh::lean_dec_ref(v_canon_6707_);
                        v___x_6709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_6708_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cacheInType_6708_);
                        if crate::leanh::lean_obj_tag(v___x_6709_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                            v_val_6710_ = crate::leanh::lean_ctor_get(v___x_6709_, 0);
                            v_isSharedCheck_6717_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6709_)) as u8;
                            if v_isSharedCheck_6717_ == 0 {
                                v___x_6712_ = v___x_6709_;
                                v_isShared_6713_ = v_isSharedCheck_6717_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6710_);
                                crate::leanh::lean_dec(v___x_6709_);
                                v___x_6712_ = crate::leanh::lean_box(0);
                                v_isShared_6713_ = v_isSharedCheck_6717_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6709_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6718_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(v___x_6654_, v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6718_) == 0 {
                                v_a_6719_ = crate::leanh::lean_ctor_get(v___x_6718_, 0);
                                v_isSharedCheck_6756_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6718_)) as u8;
                                if v_isSharedCheck_6756_ == 0 {
                                    v___x_6721_ = v___x_6718_;
                                    v_isShared_6722_ = v_isSharedCheck_6756_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6719_);
                                    crate::leanh::lean_dec(v___x_6718_);
                                    v___x_6721_ = crate::leanh::lean_box(0);
                                    v_isShared_6722_ = v_isSharedCheck_6756_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                                return v___x_6718_;
                            }
                        }
                    }
                }
                6 => {
                    if v_a_6646_ == 0 {
                        v___x_6757_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6758_ = crate::leanh::lean_ctor_get(v___x_6757_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6758_);
                        crate::leanh::lean_dec(v___x_6757_);
                        v_cache_6759_ = crate::leanh::lean_ctor_get(v_canon_6758_, 0);
                        crate::leanh::lean_inc_ref(v_cache_6759_);
                        crate::leanh::lean_dec_ref(v_canon_6758_);
                        v___x_6760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_6759_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cache_6759_);
                        if crate::leanh::lean_obj_tag(v___x_6760_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                            v_val_6761_ = crate::leanh::lean_ctor_get(v___x_6760_, 0);
                            v_isSharedCheck_6768_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6760_)) as u8;
                            if v_isSharedCheck_6768_ == 0 {
                                v___x_6763_ = v___x_6760_;
                                v_isShared_6764_ = v_isSharedCheck_6768_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6761_);
                                crate::leanh::lean_dec(v___x_6760_);
                                v___x_6763_ = crate::leanh::lean_box(0);
                                v_isShared_6764_ = v_isSharedCheck_6768_;
                                state = 17;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6760_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6769_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6769_) == 0 {
                                v_a_6770_ = crate::leanh::lean_ctor_get(v___x_6769_, 0);
                                v_isSharedCheck_6807_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6769_)) as u8;
                                if v_isSharedCheck_6807_ == 0 {
                                    v___x_6772_ = v___x_6769_;
                                    v_isShared_6773_ = v_isSharedCheck_6807_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6770_);
                                    crate::leanh::lean_dec(v___x_6769_);
                                    v___x_6772_ = crate::leanh::lean_box(0);
                                    v_isShared_6773_ = v_isSharedCheck_6807_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                                return v___x_6769_;
                            }
                        }
                    } else {
                        v___x_6808_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6809_ = crate::leanh::lean_ctor_get(v___x_6808_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6809_);
                        crate::leanh::lean_dec(v___x_6808_);
                        v_cacheInType_6810_ = crate::leanh::lean_ctor_get(v_canon_6809_, 1);
                        crate::leanh::lean_inc_ref(v_cacheInType_6810_);
                        crate::leanh::lean_dec_ref(v_canon_6809_);
                        v___x_6811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_6810_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cacheInType_6810_);
                        if crate::leanh::lean_obj_tag(v___x_6811_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                            v_val_6812_ = crate::leanh::lean_ctor_get(v___x_6811_, 0);
                            v_isSharedCheck_6819_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6811_)) as u8;
                            if v_isSharedCheck_6819_ == 0 {
                                v___x_6814_ = v___x_6811_;
                                v_isShared_6815_ = v_isSharedCheck_6819_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6812_);
                                crate::leanh::lean_dec(v___x_6811_);
                                v___x_6814_ = crate::leanh::lean_box(0);
                                v_isShared_6815_ = v_isSharedCheck_6819_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6811_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6820_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6820_) == 0 {
                                v_a_6821_ = crate::leanh::lean_ctor_get(v___x_6820_, 0);
                                v_isSharedCheck_6858_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6820_)) as u8;
                                if v_isSharedCheck_6858_ == 0 {
                                    v___x_6823_ = v___x_6820_;
                                    v_isShared_6824_ = v_isSharedCheck_6858_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6821_);
                                    crate::leanh::lean_dec(v___x_6820_);
                                    v___x_6823_ = crate::leanh::lean_box(0);
                                    v_isShared_6824_ = v_isSharedCheck_6858_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                                return v___x_6820_;
                            }
                        }
                    }
                }
                8 => {
                    v___x_6859_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___closed__0;
                    if v_a_6646_ == 0 {
                        v___x_6860_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6861_ = crate::leanh::lean_ctor_get(v___x_6860_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6861_);
                        crate::leanh::lean_dec(v___x_6860_);
                        v_cache_6862_ = crate::leanh::lean_ctor_get(v_canon_6861_, 0);
                        crate::leanh::lean_inc_ref(v_cache_6862_);
                        crate::leanh::lean_dec_ref(v_canon_6861_);
                        v___x_6863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_6862_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cache_6862_);
                        if crate::leanh::lean_obj_tag(v___x_6863_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 4);
                            v_val_6864_ = crate::leanh::lean_ctor_get(v___x_6863_, 0);
                            v_isSharedCheck_6871_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6863_)) as u8;
                            if v_isSharedCheck_6871_ == 0 {
                                v___x_6866_ = v___x_6863_;
                                v_isShared_6867_ = v_isSharedCheck_6871_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6864_);
                                crate::leanh::lean_dec(v___x_6863_);
                                v___x_6866_ = crate::leanh::lean_box(0);
                                v_isShared_6867_ = v_isSharedCheck_6871_;
                                state = 33;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6863_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6872_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_6859_, v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6872_) == 0 {
                                v_a_6873_ = crate::leanh::lean_ctor_get(v___x_6872_, 0);
                                v_isSharedCheck_6910_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6872_)) as u8;
                                if v_isSharedCheck_6910_ == 0 {
                                    v___x_6875_ = v___x_6872_;
                                    v_isShared_6876_ = v_isSharedCheck_6910_;
                                    state = 35;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6873_);
                                    crate::leanh::lean_dec(v___x_6872_);
                                    v___x_6875_ = crate::leanh::lean_box(0);
                                    v_isShared_6876_ = v_isSharedCheck_6910_;
                                    state = 35;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 4);
                                return v___x_6872_;
                            }
                        }
                    } else {
                        v___x_6911_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6912_ = crate::leanh::lean_ctor_get(v___x_6911_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6912_);
                        crate::leanh::lean_dec(v___x_6911_);
                        v_cacheInType_6913_ = crate::leanh::lean_ctor_get(v_canon_6912_, 1);
                        crate::leanh::lean_inc_ref(v_cacheInType_6913_);
                        crate::leanh::lean_dec_ref(v_canon_6912_);
                        v___x_6914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_6913_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cacheInType_6913_);
                        if crate::leanh::lean_obj_tag(v___x_6914_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 4);
                            v_val_6915_ = crate::leanh::lean_ctor_get(v___x_6914_, 0);
                            v_isSharedCheck_6922_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6914_)) as u8;
                            if v_isSharedCheck_6922_ == 0 {
                                v___x_6917_ = v___x_6914_;
                                v_isShared_6918_ = v_isSharedCheck_6922_;
                                state = 41;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6915_);
                                crate::leanh::lean_dec(v___x_6914_);
                                v___x_6917_ = crate::leanh::lean_box(0);
                                v_isShared_6918_ = v_isSharedCheck_6922_;
                                state = 41;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6914_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6923_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(v___x_6859_, v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6923_) == 0 {
                                v_a_6924_ = crate::leanh::lean_ctor_get(v___x_6923_, 0);
                                v_isSharedCheck_6961_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6923_)) as u8;
                                if v_isSharedCheck_6961_ == 0 {
                                    v___x_6926_ = v___x_6923_;
                                    v_isShared_6927_ = v_isSharedCheck_6961_;
                                    state = 43;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6924_);
                                    crate::leanh::lean_dec(v___x_6923_);
                                    v___x_6926_ = crate::leanh::lean_box(0);
                                    v_isShared_6927_ = v_isSharedCheck_6961_;
                                    state = 43;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 4);
                                return v___x_6923_;
                            }
                        }
                    }
                }
                5 => {
                    if v_a_6646_ == 0 {
                        v___x_6962_ = lean_st_ref_get(v_a_6648_);
                        v_canon_6963_ = crate::leanh::lean_ctor_get(v___x_6962_, 9);
                        crate::leanh::lean_inc_ref(v_canon_6963_);
                        crate::leanh::lean_dec(v___x_6962_);
                        v_cache_6964_ = crate::leanh::lean_ctor_get(v_canon_6963_, 0);
                        crate::leanh::lean_inc_ref(v_cache_6964_);
                        crate::leanh::lean_dec_ref(v_canon_6963_);
                        v___x_6965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_6964_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cache_6964_);
                        if crate::leanh::lean_obj_tag(v___x_6965_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 2);
                            v_val_6966_ = crate::leanh::lean_ctor_get(v___x_6965_, 0);
                            v_isSharedCheck_6973_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6965_)) as u8;
                            if v_isSharedCheck_6973_ == 0 {
                                v___x_6968_ = v___x_6965_;
                                v_isShared_6969_ = v_isSharedCheck_6973_;
                                state = 49;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_6966_);
                                crate::leanh::lean_dec(v___x_6965_);
                                v___x_6968_ = crate::leanh::lean_box(0);
                                v_isShared_6969_ = v_isSharedCheck_6973_;
                                state = 49;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6965_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_6974_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_6974_) == 0 {
                                v_a_6975_ = crate::leanh::lean_ctor_get(v___x_6974_, 0);
                                v_isSharedCheck_7012_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6974_)) as u8;
                                if v_isSharedCheck_7012_ == 0 {
                                    v___x_6977_ = v___x_6974_;
                                    v_isShared_6978_ = v_isSharedCheck_7012_;
                                    state = 51;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6975_);
                                    crate::leanh::lean_dec(v___x_6974_);
                                    v___x_6977_ = crate::leanh::lean_box(0);
                                    v_isShared_6978_ = v_isSharedCheck_7012_;
                                    state = 51;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 2);
                                return v___x_6974_;
                            }
                        }
                    } else {
                        v___x_7013_ = lean_st_ref_get(v_a_6648_);
                        v_canon_7014_ = crate::leanh::lean_ctor_get(v___x_7013_, 9);
                        crate::leanh::lean_inc_ref(v_canon_7014_);
                        crate::leanh::lean_dec(v___x_7013_);
                        v_cacheInType_7015_ = crate::leanh::lean_ctor_get(v_canon_7014_, 1);
                        crate::leanh::lean_inc_ref(v_cacheInType_7015_);
                        crate::leanh::lean_dec_ref(v_canon_7014_);
                        v___x_7016_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_7015_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cacheInType_7015_);
                        if crate::leanh::lean_obj_tag(v___x_7016_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 2);
                            v_val_7017_ = crate::leanh::lean_ctor_get(v___x_7016_, 0);
                            v_isSharedCheck_7024_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7016_)) as u8;
                            if v_isSharedCheck_7024_ == 0 {
                                v___x_7019_ = v___x_7016_;
                                v_isShared_7020_ = v_isSharedCheck_7024_;
                                state = 57;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_7017_);
                                crate::leanh::lean_dec(v___x_7016_);
                                v___x_7019_ = crate::leanh::lean_box(0);
                                v_isShared_7020_ = v_isSharedCheck_7024_;
                                state = 57;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_7016_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_7025_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_7025_) == 0 {
                                v_a_7026_ = crate::leanh::lean_ctor_get(v___x_7025_, 0);
                                v_isSharedCheck_7063_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7025_)) as u8;
                                if v_isSharedCheck_7063_ == 0 {
                                    v___x_7028_ = v___x_7025_;
                                    v_isShared_7029_ = v_isSharedCheck_7063_;
                                    state = 59;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7026_);
                                    crate::leanh::lean_dec(v___x_7025_);
                                    v___x_7028_ = crate::leanh::lean_box(0);
                                    v_isShared_7029_ = v_isSharedCheck_7063_;
                                    state = 59;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 2);
                                return v___x_7025_;
                            }
                        }
                    }
                }
                11 => {
                    if v_a_6646_ == 0 {
                        v___x_7064_ = lean_st_ref_get(v_a_6648_);
                        v_canon_7065_ = crate::leanh::lean_ctor_get(v___x_7064_, 9);
                        crate::leanh::lean_inc_ref(v_canon_7065_);
                        crate::leanh::lean_dec(v___x_7064_);
                        v_cache_7066_ = crate::leanh::lean_ctor_get(v_canon_7065_, 0);
                        crate::leanh::lean_inc_ref(v_cache_7066_);
                        crate::leanh::lean_dec_ref(v_canon_7065_);
                        v___x_7067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cache_7066_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cache_7066_);
                        if crate::leanh::lean_obj_tag(v___x_7067_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                            v_val_7068_ = crate::leanh::lean_ctor_get(v___x_7067_, 0);
                            v_isSharedCheck_7075_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7067_)) as u8;
                            if v_isSharedCheck_7075_ == 0 {
                                v___x_7070_ = v___x_7067_;
                                v_isShared_7071_ = v_isSharedCheck_7075_;
                                state = 65;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_7068_);
                                crate::leanh::lean_dec(v___x_7067_);
                                v___x_7070_ = crate::leanh::lean_box(0);
                                v_isShared_7071_ = v_isSharedCheck_7075_;
                                state = 65;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_7067_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_7076_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_7076_) == 0 {
                                v_a_7077_ = crate::leanh::lean_ctor_get(v___x_7076_, 0);
                                v_isSharedCheck_7114_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7076_)) as u8;
                                if v_isSharedCheck_7114_ == 0 {
                                    v___x_7079_ = v___x_7076_;
                                    v_isShared_7080_ = v_isSharedCheck_7114_;
                                    state = 67;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7077_);
                                    crate::leanh::lean_dec(v___x_7076_);
                                    v___x_7079_ = crate::leanh::lean_box(0);
                                    v_isShared_7080_ = v_isSharedCheck_7114_;
                                    state = 67;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                                return v___x_7076_;
                            }
                        }
                    } else {
                        v___x_7115_ = lean_st_ref_get(v_a_6648_);
                        v_canon_7116_ = crate::leanh::lean_ctor_get(v___x_7115_, 9);
                        crate::leanh::lean_inc_ref(v_canon_7116_);
                        crate::leanh::lean_dec(v___x_7115_);
                        v_cacheInType_7117_ = crate::leanh::lean_ctor_get(v_canon_7116_, 1);
                        crate::leanh::lean_inc_ref(v_cacheInType_7117_);
                        crate::leanh::lean_dec_ref(v_canon_7116_);
                        v___x_7118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_cacheInType_7117_, v_e_6645_);
                        crate::leanh::lean_dec_ref(v_cacheInType_7117_);
                        if crate::leanh::lean_obj_tag(v___x_7118_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                            v_val_7119_ = crate::leanh::lean_ctor_get(v___x_7118_, 0);
                            v_isSharedCheck_7126_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7118_)) as u8;
                            if v_isSharedCheck_7126_ == 0 {
                                v___x_7121_ = v___x_7118_;
                                v_isShared_7122_ = v_isSharedCheck_7126_;
                                state = 73;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_7119_);
                                crate::leanh::lean_dec(v___x_7118_);
                                v___x_7121_ = crate::leanh::lean_box(0);
                                v_isShared_7122_ = v_isSharedCheck_7126_;
                                state = 73;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_7118_);
                            crate::leanh::lean_inc_ref(v_e_6645_);
                            v___x_7127_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(v_e_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                            if crate::leanh::lean_obj_tag(v___x_7127_) == 0 {
                                v_a_7128_ = crate::leanh::lean_ctor_get(v___x_7127_, 0);
                                v_isSharedCheck_7165_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7127_)) as u8;
                                if v_isSharedCheck_7165_ == 0 {
                                    v___x_7130_ = v___x_7127_;
                                    v_isShared_7131_ = v_isSharedCheck_7165_;
                                    state = 75;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7128_);
                                    crate::leanh::lean_dec(v___x_7127_);
                                    v___x_7130_ = crate::leanh::lean_box(0);
                                    v_isShared_7131_ = v_isSharedCheck_7165_;
                                    state = 75;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6645_, 3);
                                return v___x_7127_;
                            }
                        }
                    }
                }
                10 => {
                    v_data_7166_ = crate::leanh::lean_ctor_get(v_e_6645_, 0);
                    v_expr_7167_ = crate::leanh::lean_ctor_get(v_e_6645_, 1);
                    crate::leanh::lean_inc_ref(v_expr_7167_);
                    v___x_7168_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                        v_expr_7167_,
                        v_a_6646_,
                        v_a_6647_,
                        v_a_6648_,
                        v_a_6649_,
                        v_a_6650_,
                        v_a_6651_,
                        v_a_6652_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7168_) == 0 {
                        v_a_7169_ = crate::leanh::lean_ctor_get(v___x_7168_, 0);
                        v_isSharedCheck_7183_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7168_)) as u8;
                        if v_isSharedCheck_7183_ == 0 {
                            v___x_7171_ = v___x_7168_;
                            v_isShared_7172_ = v_isSharedCheck_7183_;
                            state = 81;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7169_);
                            crate::leanh::lean_dec(v___x_7168_);
                            v___x_7171_ = crate::leanh::lean_box(0);
                            v_isShared_7172_ = v_isSharedCheck_7183_;
                            state = 81;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_6645_, 2);
                        return v___x_7168_;
                    }
                }
                _ => {
                    v___x_7184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7184_, 0, v_e_6645_);
                    return v___x_7184_;
                }
            },
            1 => {
                if v_isShared_6662_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6661_, 0);
                    v___x_6664_ = v___x_6661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 0, v_val_6659_);
                    v___x_6664_ = v_reuseFailAlloc_6665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6664_;
            }
            3 => {
                v___x_6672_ = lean_st_ref_take(v_a_6648_);
                v_canon_6673_ = crate::leanh::lean_ctor_get(v___x_6672_, 9);
                v_share_6674_ = crate::leanh::lean_ctor_get(v___x_6672_, 0);
                v_maxFVar_6675_ = crate::leanh::lean_ctor_get(v___x_6672_, 1);
                v_proofInstInfo_6676_ = crate::leanh::lean_ctor_get(v___x_6672_, 2);
                v_inferType_6677_ = crate::leanh::lean_ctor_get(v___x_6672_, 3);
                v_getLevel_6678_ = crate::leanh::lean_ctor_get(v___x_6672_, 4);
                v_congrInfo_6679_ = crate::leanh::lean_ctor_get(v___x_6672_, 5);
                v_defEqI_6680_ = crate::leanh::lean_ctor_get(v___x_6672_, 6);
                v_extensions_6681_ = crate::leanh::lean_ctor_get(v___x_6672_, 7);
                v_issues_6682_ = crate::leanh::lean_ctor_get(v___x_6672_, 8);
                v_debug_6683_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6672_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_6704_ = (!crate::leanh::lean_is_exclusive(v___x_6672_)) as u8;
                if v_isSharedCheck_6704_ == 0 {
                    v___x_6685_ = v___x_6672_;
                    v_isShared_6686_ = v_isSharedCheck_6704_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6673_);
                    crate::leanh::lean_inc(v_issues_6682_);
                    crate::leanh::lean_inc(v_extensions_6681_);
                    crate::leanh::lean_inc(v_defEqI_6680_);
                    crate::leanh::lean_inc(v_congrInfo_6679_);
                    crate::leanh::lean_inc(v_getLevel_6678_);
                    crate::leanh::lean_inc(v_inferType_6677_);
                    crate::leanh::lean_inc(v_proofInstInfo_6676_);
                    crate::leanh::lean_inc(v_maxFVar_6675_);
                    crate::leanh::lean_inc(v_share_6674_);
                    crate::leanh::lean_dec(v___x_6672_);
                    v___x_6685_ = crate::leanh::lean_box(0);
                    v_isShared_6686_ = v_isSharedCheck_6704_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_cache_6687_ = crate::leanh::lean_ctor_get(v_canon_6673_, 0);
                v_cacheInType_6688_ = crate::leanh::lean_ctor_get(v_canon_6673_, 1);
                v_isSharedCheck_6703_ = (!crate::leanh::lean_is_exclusive(v_canon_6673_)) as u8;
                if v_isSharedCheck_6703_ == 0 {
                    v___x_6690_ = v_canon_6673_;
                    v_isShared_6691_ = v_isSharedCheck_6703_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6688_);
                    crate::leanh::lean_inc(v_cache_6687_);
                    crate::leanh::lean_dec(v_canon_6673_);
                    v___x_6690_ = crate::leanh::lean_box(0);
                    v_isShared_6691_ = v_isSharedCheck_6703_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_6668_);
                v___x_6692_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_6687_, v_e_6645_, v_a_6668_);
                if v_isShared_6691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6690_, 0, v___x_6692_);
                    v___x_6694_ = v___x_6690_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 0, v___x_6692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6702_, 1, v_cacheInType_6688_);
                    v___x_6694_ = v_reuseFailAlloc_6702_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6685_, 9, v___x_6694_);
                    v___x_6696_ = v___x_6685_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6701_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 0, v_share_6674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 1, v_maxFVar_6675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 2, v_proofInstInfo_6676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 3, v_inferType_6677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 4, v_getLevel_6678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 5, v_congrInfo_6679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 6, v_defEqI_6680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 7, v_extensions_6681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 8, v_issues_6682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6701_, 9, v___x_6694_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6701_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6683_,
                    );
                    v___x_6696_ = v_reuseFailAlloc_6701_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6697_ = lean_st_ref_set(v_a_6648_, v___x_6696_);
                if v_isShared_6671_ == 0 {
                    v___x_6699_ = v___x_6670_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6700_, 0, v_a_6668_);
                    v___x_6699_ = v_reuseFailAlloc_6700_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6699_;
            }
            9 => {
                if v_isShared_6713_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6712_, 0);
                    v___x_6715_ = v___x_6712_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_val_6710_);
                    v___x_6715_ = v_reuseFailAlloc_6716_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6715_;
            }
            11 => {
                v___x_6723_ = lean_st_ref_take(v_a_6648_);
                v_canon_6724_ = crate::leanh::lean_ctor_get(v___x_6723_, 9);
                v_share_6725_ = crate::leanh::lean_ctor_get(v___x_6723_, 0);
                v_maxFVar_6726_ = crate::leanh::lean_ctor_get(v___x_6723_, 1);
                v_proofInstInfo_6727_ = crate::leanh::lean_ctor_get(v___x_6723_, 2);
                v_inferType_6728_ = crate::leanh::lean_ctor_get(v___x_6723_, 3);
                v_getLevel_6729_ = crate::leanh::lean_ctor_get(v___x_6723_, 4);
                v_congrInfo_6730_ = crate::leanh::lean_ctor_get(v___x_6723_, 5);
                v_defEqI_6731_ = crate::leanh::lean_ctor_get(v___x_6723_, 6);
                v_extensions_6732_ = crate::leanh::lean_ctor_get(v___x_6723_, 7);
                v_issues_6733_ = crate::leanh::lean_ctor_get(v___x_6723_, 8);
                v_debug_6734_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_6755_ = (!crate::leanh::lean_is_exclusive(v___x_6723_)) as u8;
                if v_isSharedCheck_6755_ == 0 {
                    v___x_6736_ = v___x_6723_;
                    v_isShared_6737_ = v_isSharedCheck_6755_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6724_);
                    crate::leanh::lean_inc(v_issues_6733_);
                    crate::leanh::lean_inc(v_extensions_6732_);
                    crate::leanh::lean_inc(v_defEqI_6731_);
                    crate::leanh::lean_inc(v_congrInfo_6730_);
                    crate::leanh::lean_inc(v_getLevel_6729_);
                    crate::leanh::lean_inc(v_inferType_6728_);
                    crate::leanh::lean_inc(v_proofInstInfo_6727_);
                    crate::leanh::lean_inc(v_maxFVar_6726_);
                    crate::leanh::lean_inc(v_share_6725_);
                    crate::leanh::lean_dec(v___x_6723_);
                    v___x_6736_ = crate::leanh::lean_box(0);
                    v_isShared_6737_ = v_isSharedCheck_6755_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_cache_6738_ = crate::leanh::lean_ctor_get(v_canon_6724_, 0);
                v_cacheInType_6739_ = crate::leanh::lean_ctor_get(v_canon_6724_, 1);
                v_isSharedCheck_6754_ = (!crate::leanh::lean_is_exclusive(v_canon_6724_)) as u8;
                if v_isSharedCheck_6754_ == 0 {
                    v___x_6741_ = v_canon_6724_;
                    v_isShared_6742_ = v_isSharedCheck_6754_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6739_);
                    crate::leanh::lean_inc(v_cache_6738_);
                    crate::leanh::lean_dec(v_canon_6724_);
                    v___x_6741_ = crate::leanh::lean_box(0);
                    v_isShared_6742_ = v_isSharedCheck_6754_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc(v_a_6719_);
                v___x_6743_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_6739_, v_e_6645_, v_a_6719_);
                if v_isShared_6742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6741_, 1, v___x_6743_);
                    v___x_6745_ = v___x_6741_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_cache_6738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6753_, 1, v___x_6743_);
                    v___x_6745_ = v_reuseFailAlloc_6753_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_6737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6736_, 9, v___x_6745_);
                    v___x_6747_ = v___x_6736_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6752_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 0, v_share_6725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 1, v_maxFVar_6726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 2, v_proofInstInfo_6727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 3, v_inferType_6728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 4, v_getLevel_6729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 5, v_congrInfo_6730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 6, v_defEqI_6731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 7, v_extensions_6732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 8, v_issues_6733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 9, v___x_6745_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6752_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6734_,
                    );
                    v___x_6747_ = v_reuseFailAlloc_6752_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_6748_ = lean_st_ref_set(v_a_6648_, v___x_6747_);
                if v_isShared_6722_ == 0 {
                    v___x_6750_ = v___x_6721_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_a_6719_);
                    v___x_6750_ = v_reuseFailAlloc_6751_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6750_;
            }
            17 => {
                if v_isShared_6764_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6763_, 0);
                    v___x_6766_ = v___x_6763_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_val_6761_);
                    v___x_6766_ = v_reuseFailAlloc_6767_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6766_;
            }
            19 => {
                v___x_6774_ = lean_st_ref_take(v_a_6648_);
                v_canon_6775_ = crate::leanh::lean_ctor_get(v___x_6774_, 9);
                v_share_6776_ = crate::leanh::lean_ctor_get(v___x_6774_, 0);
                v_maxFVar_6777_ = crate::leanh::lean_ctor_get(v___x_6774_, 1);
                v_proofInstInfo_6778_ = crate::leanh::lean_ctor_get(v___x_6774_, 2);
                v_inferType_6779_ = crate::leanh::lean_ctor_get(v___x_6774_, 3);
                v_getLevel_6780_ = crate::leanh::lean_ctor_get(v___x_6774_, 4);
                v_congrInfo_6781_ = crate::leanh::lean_ctor_get(v___x_6774_, 5);
                v_defEqI_6782_ = crate::leanh::lean_ctor_get(v___x_6774_, 6);
                v_extensions_6783_ = crate::leanh::lean_ctor_get(v___x_6774_, 7);
                v_issues_6784_ = crate::leanh::lean_ctor_get(v___x_6774_, 8);
                v_debug_6785_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6774_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_6806_ = (!crate::leanh::lean_is_exclusive(v___x_6774_)) as u8;
                if v_isSharedCheck_6806_ == 0 {
                    v___x_6787_ = v___x_6774_;
                    v_isShared_6788_ = v_isSharedCheck_6806_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6775_);
                    crate::leanh::lean_inc(v_issues_6784_);
                    crate::leanh::lean_inc(v_extensions_6783_);
                    crate::leanh::lean_inc(v_defEqI_6782_);
                    crate::leanh::lean_inc(v_congrInfo_6781_);
                    crate::leanh::lean_inc(v_getLevel_6780_);
                    crate::leanh::lean_inc(v_inferType_6779_);
                    crate::leanh::lean_inc(v_proofInstInfo_6778_);
                    crate::leanh::lean_inc(v_maxFVar_6777_);
                    crate::leanh::lean_inc(v_share_6776_);
                    crate::leanh::lean_dec(v___x_6774_);
                    v___x_6787_ = crate::leanh::lean_box(0);
                    v_isShared_6788_ = v_isSharedCheck_6806_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_cache_6789_ = crate::leanh::lean_ctor_get(v_canon_6775_, 0);
                v_cacheInType_6790_ = crate::leanh::lean_ctor_get(v_canon_6775_, 1);
                v_isSharedCheck_6805_ = (!crate::leanh::lean_is_exclusive(v_canon_6775_)) as u8;
                if v_isSharedCheck_6805_ == 0 {
                    v___x_6792_ = v_canon_6775_;
                    v_isShared_6793_ = v_isSharedCheck_6805_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6790_);
                    crate::leanh::lean_inc(v_cache_6789_);
                    crate::leanh::lean_dec(v_canon_6775_);
                    v___x_6792_ = crate::leanh::lean_box(0);
                    v_isShared_6793_ = v_isSharedCheck_6805_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_inc(v_a_6770_);
                v___x_6794_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_6789_, v_e_6645_, v_a_6770_);
                if v_isShared_6793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6792_, 0, v___x_6794_);
                    v___x_6796_ = v___x_6792_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6804_, 0, v___x_6794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6804_, 1, v_cacheInType_6790_);
                    v___x_6796_ = v_reuseFailAlloc_6804_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_6788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6787_, 9, v___x_6796_);
                    v___x_6798_ = v___x_6787_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6803_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 0, v_share_6776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 1, v_maxFVar_6777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 2, v_proofInstInfo_6778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 3, v_inferType_6779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 4, v_getLevel_6780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 5, v_congrInfo_6781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 6, v_defEqI_6782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 7, v_extensions_6783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 8, v_issues_6784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 9, v___x_6796_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6803_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6785_,
                    );
                    v___x_6798_ = v_reuseFailAlloc_6803_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_6799_ = lean_st_ref_set(v_a_6648_, v___x_6798_);
                if v_isShared_6773_ == 0 {
                    v___x_6801_ = v___x_6772_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 0, v_a_6770_);
                    v___x_6801_ = v_reuseFailAlloc_6802_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6801_;
            }
            25 => {
                if v_isShared_6815_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6814_, 0);
                    v___x_6817_ = v___x_6814_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_val_6812_);
                    v___x_6817_ = v_reuseFailAlloc_6818_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6817_;
            }
            27 => {
                v___x_6825_ = lean_st_ref_take(v_a_6648_);
                v_canon_6826_ = crate::leanh::lean_ctor_get(v___x_6825_, 9);
                v_share_6827_ = crate::leanh::lean_ctor_get(v___x_6825_, 0);
                v_maxFVar_6828_ = crate::leanh::lean_ctor_get(v___x_6825_, 1);
                v_proofInstInfo_6829_ = crate::leanh::lean_ctor_get(v___x_6825_, 2);
                v_inferType_6830_ = crate::leanh::lean_ctor_get(v___x_6825_, 3);
                v_getLevel_6831_ = crate::leanh::lean_ctor_get(v___x_6825_, 4);
                v_congrInfo_6832_ = crate::leanh::lean_ctor_get(v___x_6825_, 5);
                v_defEqI_6833_ = crate::leanh::lean_ctor_get(v___x_6825_, 6);
                v_extensions_6834_ = crate::leanh::lean_ctor_get(v___x_6825_, 7);
                v_issues_6835_ = crate::leanh::lean_ctor_get(v___x_6825_, 8);
                v_debug_6836_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6825_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_6857_ = (!crate::leanh::lean_is_exclusive(v___x_6825_)) as u8;
                if v_isSharedCheck_6857_ == 0 {
                    v___x_6838_ = v___x_6825_;
                    v_isShared_6839_ = v_isSharedCheck_6857_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6826_);
                    crate::leanh::lean_inc(v_issues_6835_);
                    crate::leanh::lean_inc(v_extensions_6834_);
                    crate::leanh::lean_inc(v_defEqI_6833_);
                    crate::leanh::lean_inc(v_congrInfo_6832_);
                    crate::leanh::lean_inc(v_getLevel_6831_);
                    crate::leanh::lean_inc(v_inferType_6830_);
                    crate::leanh::lean_inc(v_proofInstInfo_6829_);
                    crate::leanh::lean_inc(v_maxFVar_6828_);
                    crate::leanh::lean_inc(v_share_6827_);
                    crate::leanh::lean_dec(v___x_6825_);
                    v___x_6838_ = crate::leanh::lean_box(0);
                    v_isShared_6839_ = v_isSharedCheck_6857_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v_cache_6840_ = crate::leanh::lean_ctor_get(v_canon_6826_, 0);
                v_cacheInType_6841_ = crate::leanh::lean_ctor_get(v_canon_6826_, 1);
                v_isSharedCheck_6856_ = (!crate::leanh::lean_is_exclusive(v_canon_6826_)) as u8;
                if v_isSharedCheck_6856_ == 0 {
                    v___x_6843_ = v_canon_6826_;
                    v_isShared_6844_ = v_isSharedCheck_6856_;
                    state = 29;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6841_);
                    crate::leanh::lean_inc(v_cache_6840_);
                    crate::leanh::lean_dec(v_canon_6826_);
                    v___x_6843_ = crate::leanh::lean_box(0);
                    v_isShared_6844_ = v_isSharedCheck_6856_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                crate::leanh::lean_inc(v_a_6821_);
                v___x_6845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_6841_, v_e_6645_, v_a_6821_);
                if v_isShared_6844_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6843_, 1, v___x_6845_);
                    v___x_6847_ = v___x_6843_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6855_, 0, v_cache_6840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6855_, 1, v___x_6845_);
                    v___x_6847_ = v_reuseFailAlloc_6855_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_6839_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6838_, 9, v___x_6847_);
                    v___x_6849_ = v___x_6838_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6854_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 0, v_share_6827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 1, v_maxFVar_6828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 2, v_proofInstInfo_6829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 3, v_inferType_6830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 4, v_getLevel_6831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 5, v_congrInfo_6832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 6, v_defEqI_6833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 7, v_extensions_6834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 8, v_issues_6835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6854_, 9, v___x_6847_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6854_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6836_,
                    );
                    v___x_6849_ = v_reuseFailAlloc_6854_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_6850_ = lean_st_ref_set(v_a_6648_, v___x_6849_);
                if v_isShared_6824_ == 0 {
                    v___x_6852_ = v___x_6823_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6853_, 0, v_a_6821_);
                    v___x_6852_ = v_reuseFailAlloc_6853_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6852_;
            }
            33 => {
                if v_isShared_6867_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6866_, 0);
                    v___x_6869_ = v___x_6866_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6870_, 0, v_val_6864_);
                    v___x_6869_ = v_reuseFailAlloc_6870_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6869_;
            }
            35 => {
                v___x_6877_ = lean_st_ref_take(v_a_6648_);
                v_canon_6878_ = crate::leanh::lean_ctor_get(v___x_6877_, 9);
                v_share_6879_ = crate::leanh::lean_ctor_get(v___x_6877_, 0);
                v_maxFVar_6880_ = crate::leanh::lean_ctor_get(v___x_6877_, 1);
                v_proofInstInfo_6881_ = crate::leanh::lean_ctor_get(v___x_6877_, 2);
                v_inferType_6882_ = crate::leanh::lean_ctor_get(v___x_6877_, 3);
                v_getLevel_6883_ = crate::leanh::lean_ctor_get(v___x_6877_, 4);
                v_congrInfo_6884_ = crate::leanh::lean_ctor_get(v___x_6877_, 5);
                v_defEqI_6885_ = crate::leanh::lean_ctor_get(v___x_6877_, 6);
                v_extensions_6886_ = crate::leanh::lean_ctor_get(v___x_6877_, 7);
                v_issues_6887_ = crate::leanh::lean_ctor_get(v___x_6877_, 8);
                v_debug_6888_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6877_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_6909_ = (!crate::leanh::lean_is_exclusive(v___x_6877_)) as u8;
                if v_isSharedCheck_6909_ == 0 {
                    v___x_6890_ = v___x_6877_;
                    v_isShared_6891_ = v_isSharedCheck_6909_;
                    state = 36;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6878_);
                    crate::leanh::lean_inc(v_issues_6887_);
                    crate::leanh::lean_inc(v_extensions_6886_);
                    crate::leanh::lean_inc(v_defEqI_6885_);
                    crate::leanh::lean_inc(v_congrInfo_6884_);
                    crate::leanh::lean_inc(v_getLevel_6883_);
                    crate::leanh::lean_inc(v_inferType_6882_);
                    crate::leanh::lean_inc(v_proofInstInfo_6881_);
                    crate::leanh::lean_inc(v_maxFVar_6880_);
                    crate::leanh::lean_inc(v_share_6879_);
                    crate::leanh::lean_dec(v___x_6877_);
                    v___x_6890_ = crate::leanh::lean_box(0);
                    v_isShared_6891_ = v_isSharedCheck_6909_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v_cache_6892_ = crate::leanh::lean_ctor_get(v_canon_6878_, 0);
                v_cacheInType_6893_ = crate::leanh::lean_ctor_get(v_canon_6878_, 1);
                v_isSharedCheck_6908_ = (!crate::leanh::lean_is_exclusive(v_canon_6878_)) as u8;
                if v_isSharedCheck_6908_ == 0 {
                    v___x_6895_ = v_canon_6878_;
                    v_isShared_6896_ = v_isSharedCheck_6908_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6893_);
                    crate::leanh::lean_inc(v_cache_6892_);
                    crate::leanh::lean_dec(v_canon_6878_);
                    v___x_6895_ = crate::leanh::lean_box(0);
                    v_isShared_6896_ = v_isSharedCheck_6908_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                crate::leanh::lean_inc(v_a_6873_);
                v___x_6897_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_6892_, v_e_6645_, v_a_6873_);
                if v_isShared_6896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6895_, 0, v___x_6897_);
                    v___x_6899_ = v___x_6895_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_6907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 0, v___x_6897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 1, v_cacheInType_6893_);
                    v___x_6899_ = v_reuseFailAlloc_6907_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_6891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6890_, 9, v___x_6899_);
                    v___x_6901_ = v___x_6890_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6906_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 0, v_share_6879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 1, v_maxFVar_6880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 2, v_proofInstInfo_6881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 3, v_inferType_6882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 4, v_getLevel_6883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 5, v_congrInfo_6884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 6, v_defEqI_6885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 7, v_extensions_6886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 8, v_issues_6887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6906_, 9, v___x_6899_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6906_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6888_,
                    );
                    v___x_6901_ = v_reuseFailAlloc_6906_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_6902_ = lean_st_ref_set(v_a_6648_, v___x_6901_);
                if v_isShared_6876_ == 0 {
                    v___x_6904_ = v___x_6875_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6905_, 0, v_a_6873_);
                    v___x_6904_ = v_reuseFailAlloc_6905_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_6904_;
            }
            41 => {
                if v_isShared_6918_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6917_, 0);
                    v___x_6920_ = v___x_6917_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6921_, 0, v_val_6915_);
                    v___x_6920_ = v_reuseFailAlloc_6921_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_6920_;
            }
            43 => {
                v___x_6928_ = lean_st_ref_take(v_a_6648_);
                v_canon_6929_ = crate::leanh::lean_ctor_get(v___x_6928_, 9);
                v_share_6930_ = crate::leanh::lean_ctor_get(v___x_6928_, 0);
                v_maxFVar_6931_ = crate::leanh::lean_ctor_get(v___x_6928_, 1);
                v_proofInstInfo_6932_ = crate::leanh::lean_ctor_get(v___x_6928_, 2);
                v_inferType_6933_ = crate::leanh::lean_ctor_get(v___x_6928_, 3);
                v_getLevel_6934_ = crate::leanh::lean_ctor_get(v___x_6928_, 4);
                v_congrInfo_6935_ = crate::leanh::lean_ctor_get(v___x_6928_, 5);
                v_defEqI_6936_ = crate::leanh::lean_ctor_get(v___x_6928_, 6);
                v_extensions_6937_ = crate::leanh::lean_ctor_get(v___x_6928_, 7);
                v_issues_6938_ = crate::leanh::lean_ctor_get(v___x_6928_, 8);
                v_debug_6939_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6928_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_6960_ = (!crate::leanh::lean_is_exclusive(v___x_6928_)) as u8;
                if v_isSharedCheck_6960_ == 0 {
                    v___x_6941_ = v___x_6928_;
                    v_isShared_6942_ = v_isSharedCheck_6960_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6929_);
                    crate::leanh::lean_inc(v_issues_6938_);
                    crate::leanh::lean_inc(v_extensions_6937_);
                    crate::leanh::lean_inc(v_defEqI_6936_);
                    crate::leanh::lean_inc(v_congrInfo_6935_);
                    crate::leanh::lean_inc(v_getLevel_6934_);
                    crate::leanh::lean_inc(v_inferType_6933_);
                    crate::leanh::lean_inc(v_proofInstInfo_6932_);
                    crate::leanh::lean_inc(v_maxFVar_6931_);
                    crate::leanh::lean_inc(v_share_6930_);
                    crate::leanh::lean_dec(v___x_6928_);
                    v___x_6941_ = crate::leanh::lean_box(0);
                    v_isShared_6942_ = v_isSharedCheck_6960_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v_cache_6943_ = crate::leanh::lean_ctor_get(v_canon_6929_, 0);
                v_cacheInType_6944_ = crate::leanh::lean_ctor_get(v_canon_6929_, 1);
                v_isSharedCheck_6959_ = (!crate::leanh::lean_is_exclusive(v_canon_6929_)) as u8;
                if v_isSharedCheck_6959_ == 0 {
                    v___x_6946_ = v_canon_6929_;
                    v_isShared_6947_ = v_isSharedCheck_6959_;
                    state = 45;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6944_);
                    crate::leanh::lean_inc(v_cache_6943_);
                    crate::leanh::lean_dec(v_canon_6929_);
                    v___x_6946_ = crate::leanh::lean_box(0);
                    v_isShared_6947_ = v_isSharedCheck_6959_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                crate::leanh::lean_inc(v_a_6924_);
                v___x_6948_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_6944_, v_e_6645_, v_a_6924_);
                if v_isShared_6947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6946_, 1, v___x_6948_);
                    v___x_6950_ = v___x_6946_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_cache_6943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6958_, 1, v___x_6948_);
                    v___x_6950_ = v_reuseFailAlloc_6958_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_6942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6941_, 9, v___x_6950_);
                    v___x_6952_ = v___x_6941_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_6957_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 0, v_share_6930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 1, v_maxFVar_6931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 2, v_proofInstInfo_6932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 3, v_inferType_6933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 4, v_getLevel_6934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 5, v_congrInfo_6935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 6, v_defEqI_6936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 7, v_extensions_6937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 8, v_issues_6938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 9, v___x_6950_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6957_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6939_,
                    );
                    v___x_6952_ = v_reuseFailAlloc_6957_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___x_6953_ = lean_st_ref_set(v_a_6648_, v___x_6952_);
                if v_isShared_6927_ == 0 {
                    v___x_6955_ = v___x_6926_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6956_, 0, v_a_6924_);
                    v___x_6955_ = v_reuseFailAlloc_6956_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_6955_;
            }
            49 => {
                if v_isShared_6969_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6968_, 0);
                    v___x_6971_ = v___x_6968_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_6972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6972_, 0, v_val_6966_);
                    v___x_6971_ = v_reuseFailAlloc_6972_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_6971_;
            }
            51 => {
                v___x_6979_ = lean_st_ref_take(v_a_6648_);
                v_canon_6980_ = crate::leanh::lean_ctor_get(v___x_6979_, 9);
                v_share_6981_ = crate::leanh::lean_ctor_get(v___x_6979_, 0);
                v_maxFVar_6982_ = crate::leanh::lean_ctor_get(v___x_6979_, 1);
                v_proofInstInfo_6983_ = crate::leanh::lean_ctor_get(v___x_6979_, 2);
                v_inferType_6984_ = crate::leanh::lean_ctor_get(v___x_6979_, 3);
                v_getLevel_6985_ = crate::leanh::lean_ctor_get(v___x_6979_, 4);
                v_congrInfo_6986_ = crate::leanh::lean_ctor_get(v___x_6979_, 5);
                v_defEqI_6987_ = crate::leanh::lean_ctor_get(v___x_6979_, 6);
                v_extensions_6988_ = crate::leanh::lean_ctor_get(v___x_6979_, 7);
                v_issues_6989_ = crate::leanh::lean_ctor_get(v___x_6979_, 8);
                v_debug_6990_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_6979_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_7011_ = (!crate::leanh::lean_is_exclusive(v___x_6979_)) as u8;
                if v_isSharedCheck_7011_ == 0 {
                    v___x_6992_ = v___x_6979_;
                    v_isShared_6993_ = v_isSharedCheck_7011_;
                    state = 52;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_6980_);
                    crate::leanh::lean_inc(v_issues_6989_);
                    crate::leanh::lean_inc(v_extensions_6988_);
                    crate::leanh::lean_inc(v_defEqI_6987_);
                    crate::leanh::lean_inc(v_congrInfo_6986_);
                    crate::leanh::lean_inc(v_getLevel_6985_);
                    crate::leanh::lean_inc(v_inferType_6984_);
                    crate::leanh::lean_inc(v_proofInstInfo_6983_);
                    crate::leanh::lean_inc(v_maxFVar_6982_);
                    crate::leanh::lean_inc(v_share_6981_);
                    crate::leanh::lean_dec(v___x_6979_);
                    v___x_6992_ = crate::leanh::lean_box(0);
                    v_isShared_6993_ = v_isSharedCheck_7011_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v_cache_6994_ = crate::leanh::lean_ctor_get(v_canon_6980_, 0);
                v_cacheInType_6995_ = crate::leanh::lean_ctor_get(v_canon_6980_, 1);
                v_isSharedCheck_7010_ = (!crate::leanh::lean_is_exclusive(v_canon_6980_)) as u8;
                if v_isSharedCheck_7010_ == 0 {
                    v___x_6997_ = v_canon_6980_;
                    v_isShared_6998_ = v_isSharedCheck_7010_;
                    state = 53;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_6995_);
                    crate::leanh::lean_inc(v_cache_6994_);
                    crate::leanh::lean_dec(v_canon_6980_);
                    v___x_6997_ = crate::leanh::lean_box(0);
                    v_isShared_6998_ = v_isSharedCheck_7010_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                crate::leanh::lean_inc(v_a_6975_);
                v___x_6999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_6994_, v_e_6645_, v_a_6975_);
                if v_isShared_6998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6997_, 0, v___x_6999_);
                    v___x_7001_ = v___x_6997_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7009_, 0, v___x_6999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7009_, 1, v_cacheInType_6995_);
                    v___x_7001_ = v_reuseFailAlloc_7009_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                if v_isShared_6993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6992_, 9, v___x_7001_);
                    v___x_7003_ = v___x_6992_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_7008_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 0, v_share_6981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 1, v_maxFVar_6982_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 2, v_proofInstInfo_6983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 3, v_inferType_6984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 4, v_getLevel_6985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 5, v_congrInfo_6986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 6, v_defEqI_6987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 7, v_extensions_6988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 8, v_issues_6989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7008_, 9, v___x_7001_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7008_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_6990_,
                    );
                    v___x_7003_ = v_reuseFailAlloc_7008_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                v___x_7004_ = lean_st_ref_set(v_a_6648_, v___x_7003_);
                if v_isShared_6978_ == 0 {
                    v___x_7006_ = v___x_6977_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_7007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 0, v_a_6975_);
                    v___x_7006_ = v_reuseFailAlloc_7007_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_7006_;
            }
            57 => {
                if v_isShared_7020_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7019_, 0);
                    v___x_7022_ = v___x_7019_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_7023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7023_, 0, v_val_7017_);
                    v___x_7022_ = v_reuseFailAlloc_7023_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_7022_;
            }
            59 => {
                v___x_7030_ = lean_st_ref_take(v_a_6648_);
                v_canon_7031_ = crate::leanh::lean_ctor_get(v___x_7030_, 9);
                v_share_7032_ = crate::leanh::lean_ctor_get(v___x_7030_, 0);
                v_maxFVar_7033_ = crate::leanh::lean_ctor_get(v___x_7030_, 1);
                v_proofInstInfo_7034_ = crate::leanh::lean_ctor_get(v___x_7030_, 2);
                v_inferType_7035_ = crate::leanh::lean_ctor_get(v___x_7030_, 3);
                v_getLevel_7036_ = crate::leanh::lean_ctor_get(v___x_7030_, 4);
                v_congrInfo_7037_ = crate::leanh::lean_ctor_get(v___x_7030_, 5);
                v_defEqI_7038_ = crate::leanh::lean_ctor_get(v___x_7030_, 6);
                v_extensions_7039_ = crate::leanh::lean_ctor_get(v___x_7030_, 7);
                v_issues_7040_ = crate::leanh::lean_ctor_get(v___x_7030_, 8);
                v_debug_7041_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_7030_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_7062_ = (!crate::leanh::lean_is_exclusive(v___x_7030_)) as u8;
                if v_isSharedCheck_7062_ == 0 {
                    v___x_7043_ = v___x_7030_;
                    v_isShared_7044_ = v_isSharedCheck_7062_;
                    state = 60;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_7031_);
                    crate::leanh::lean_inc(v_issues_7040_);
                    crate::leanh::lean_inc(v_extensions_7039_);
                    crate::leanh::lean_inc(v_defEqI_7038_);
                    crate::leanh::lean_inc(v_congrInfo_7037_);
                    crate::leanh::lean_inc(v_getLevel_7036_);
                    crate::leanh::lean_inc(v_inferType_7035_);
                    crate::leanh::lean_inc(v_proofInstInfo_7034_);
                    crate::leanh::lean_inc(v_maxFVar_7033_);
                    crate::leanh::lean_inc(v_share_7032_);
                    crate::leanh::lean_dec(v___x_7030_);
                    v___x_7043_ = crate::leanh::lean_box(0);
                    v_isShared_7044_ = v_isSharedCheck_7062_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v_cache_7045_ = crate::leanh::lean_ctor_get(v_canon_7031_, 0);
                v_cacheInType_7046_ = crate::leanh::lean_ctor_get(v_canon_7031_, 1);
                v_isSharedCheck_7061_ = (!crate::leanh::lean_is_exclusive(v_canon_7031_)) as u8;
                if v_isSharedCheck_7061_ == 0 {
                    v___x_7048_ = v_canon_7031_;
                    v_isShared_7049_ = v_isSharedCheck_7061_;
                    state = 61;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_7046_);
                    crate::leanh::lean_inc(v_cache_7045_);
                    crate::leanh::lean_dec(v_canon_7031_);
                    v___x_7048_ = crate::leanh::lean_box(0);
                    v_isShared_7049_ = v_isSharedCheck_7061_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                crate::leanh::lean_inc(v_a_7026_);
                v___x_7050_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_7046_, v_e_6645_, v_a_7026_);
                if v_isShared_7049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7048_, 1, v___x_7050_);
                    v___x_7052_ = v___x_7048_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_7060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7060_, 0, v_cache_7045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7060_, 1, v___x_7050_);
                    v___x_7052_ = v_reuseFailAlloc_7060_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                if v_isShared_7044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7043_, 9, v___x_7052_);
                    v___x_7054_ = v___x_7043_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_7059_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_share_7032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 1, v_maxFVar_7033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 2, v_proofInstInfo_7034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 3, v_inferType_7035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 4, v_getLevel_7036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 5, v_congrInfo_7037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 6, v_defEqI_7038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 7, v_extensions_7039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 8, v_issues_7040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 9, v___x_7052_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7059_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_7041_,
                    );
                    v___x_7054_ = v_reuseFailAlloc_7059_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                v___x_7055_ = lean_st_ref_set(v_a_6648_, v___x_7054_);
                if v_isShared_7029_ == 0 {
                    v___x_7057_ = v___x_7028_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_7058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_a_7026_);
                    v___x_7057_ = v_reuseFailAlloc_7058_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_7057_;
            }
            65 => {
                if v_isShared_7071_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7070_, 0);
                    v___x_7073_ = v___x_7070_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_7074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7074_, 0, v_val_7068_);
                    v___x_7073_ = v_reuseFailAlloc_7074_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_7073_;
            }
            67 => {
                v___x_7081_ = lean_st_ref_take(v_a_6648_);
                v_canon_7082_ = crate::leanh::lean_ctor_get(v___x_7081_, 9);
                v_share_7083_ = crate::leanh::lean_ctor_get(v___x_7081_, 0);
                v_maxFVar_7084_ = crate::leanh::lean_ctor_get(v___x_7081_, 1);
                v_proofInstInfo_7085_ = crate::leanh::lean_ctor_get(v___x_7081_, 2);
                v_inferType_7086_ = crate::leanh::lean_ctor_get(v___x_7081_, 3);
                v_getLevel_7087_ = crate::leanh::lean_ctor_get(v___x_7081_, 4);
                v_congrInfo_7088_ = crate::leanh::lean_ctor_get(v___x_7081_, 5);
                v_defEqI_7089_ = crate::leanh::lean_ctor_get(v___x_7081_, 6);
                v_extensions_7090_ = crate::leanh::lean_ctor_get(v___x_7081_, 7);
                v_issues_7091_ = crate::leanh::lean_ctor_get(v___x_7081_, 8);
                v_debug_7092_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_7081_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_7113_ = (!crate::leanh::lean_is_exclusive(v___x_7081_)) as u8;
                if v_isSharedCheck_7113_ == 0 {
                    v___x_7094_ = v___x_7081_;
                    v_isShared_7095_ = v_isSharedCheck_7113_;
                    state = 68;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_7082_);
                    crate::leanh::lean_inc(v_issues_7091_);
                    crate::leanh::lean_inc(v_extensions_7090_);
                    crate::leanh::lean_inc(v_defEqI_7089_);
                    crate::leanh::lean_inc(v_congrInfo_7088_);
                    crate::leanh::lean_inc(v_getLevel_7087_);
                    crate::leanh::lean_inc(v_inferType_7086_);
                    crate::leanh::lean_inc(v_proofInstInfo_7085_);
                    crate::leanh::lean_inc(v_maxFVar_7084_);
                    crate::leanh::lean_inc(v_share_7083_);
                    crate::leanh::lean_dec(v___x_7081_);
                    v___x_7094_ = crate::leanh::lean_box(0);
                    v_isShared_7095_ = v_isSharedCheck_7113_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                v_cache_7096_ = crate::leanh::lean_ctor_get(v_canon_7082_, 0);
                v_cacheInType_7097_ = crate::leanh::lean_ctor_get(v_canon_7082_, 1);
                v_isSharedCheck_7112_ = (!crate::leanh::lean_is_exclusive(v_canon_7082_)) as u8;
                if v_isSharedCheck_7112_ == 0 {
                    v___x_7099_ = v_canon_7082_;
                    v_isShared_7100_ = v_isSharedCheck_7112_;
                    state = 69;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_7097_);
                    crate::leanh::lean_inc(v_cache_7096_);
                    crate::leanh::lean_dec(v_canon_7082_);
                    v___x_7099_ = crate::leanh::lean_box(0);
                    v_isShared_7100_ = v_isSharedCheck_7112_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                crate::leanh::lean_inc(v_a_7077_);
                v___x_7101_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cache_7096_, v_e_6645_, v_a_7077_);
                if v_isShared_7100_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7099_, 0, v___x_7101_);
                    v___x_7103_ = v___x_7099_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_7111_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7111_, 0, v___x_7101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7111_, 1, v_cacheInType_7097_);
                    v___x_7103_ = v_reuseFailAlloc_7111_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_7095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7094_, 9, v___x_7103_);
                    v___x_7105_ = v___x_7094_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_7110_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 0, v_share_7083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 1, v_maxFVar_7084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 2, v_proofInstInfo_7085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 3, v_inferType_7086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 4, v_getLevel_7087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 5, v_congrInfo_7088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 6, v_defEqI_7089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 7, v_extensions_7090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 8, v_issues_7091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7110_, 9, v___x_7103_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7110_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_7092_,
                    );
                    v___x_7105_ = v_reuseFailAlloc_7110_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                v___x_7106_ = lean_st_ref_set(v_a_6648_, v___x_7105_);
                if v_isShared_7080_ == 0 {
                    v___x_7108_ = v___x_7079_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_7109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7109_, 0, v_a_7077_);
                    v___x_7108_ = v_reuseFailAlloc_7109_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_7108_;
            }
            73 => {
                if v_isShared_7122_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7121_, 0);
                    v___x_7124_ = v___x_7121_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_7125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7125_, 0, v_val_7119_);
                    v___x_7124_ = v_reuseFailAlloc_7125_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_7124_;
            }
            75 => {
                v___x_7132_ = lean_st_ref_take(v_a_6648_);
                v_canon_7133_ = crate::leanh::lean_ctor_get(v___x_7132_, 9);
                v_share_7134_ = crate::leanh::lean_ctor_get(v___x_7132_, 0);
                v_maxFVar_7135_ = crate::leanh::lean_ctor_get(v___x_7132_, 1);
                v_proofInstInfo_7136_ = crate::leanh::lean_ctor_get(v___x_7132_, 2);
                v_inferType_7137_ = crate::leanh::lean_ctor_get(v___x_7132_, 3);
                v_getLevel_7138_ = crate::leanh::lean_ctor_get(v___x_7132_, 4);
                v_congrInfo_7139_ = crate::leanh::lean_ctor_get(v___x_7132_, 5);
                v_defEqI_7140_ = crate::leanh::lean_ctor_get(v___x_7132_, 6);
                v_extensions_7141_ = crate::leanh::lean_ctor_get(v___x_7132_, 7);
                v_issues_7142_ = crate::leanh::lean_ctor_get(v___x_7132_, 8);
                v_debug_7143_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_7132_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_7164_ = (!crate::leanh::lean_is_exclusive(v___x_7132_)) as u8;
                if v_isSharedCheck_7164_ == 0 {
                    v___x_7145_ = v___x_7132_;
                    v_isShared_7146_ = v_isSharedCheck_7164_;
                    state = 76;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_7133_);
                    crate::leanh::lean_inc(v_issues_7142_);
                    crate::leanh::lean_inc(v_extensions_7141_);
                    crate::leanh::lean_inc(v_defEqI_7140_);
                    crate::leanh::lean_inc(v_congrInfo_7139_);
                    crate::leanh::lean_inc(v_getLevel_7138_);
                    crate::leanh::lean_inc(v_inferType_7137_);
                    crate::leanh::lean_inc(v_proofInstInfo_7136_);
                    crate::leanh::lean_inc(v_maxFVar_7135_);
                    crate::leanh::lean_inc(v_share_7134_);
                    crate::leanh::lean_dec(v___x_7132_);
                    v___x_7145_ = crate::leanh::lean_box(0);
                    v_isShared_7146_ = v_isSharedCheck_7164_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                v_cache_7147_ = crate::leanh::lean_ctor_get(v_canon_7133_, 0);
                v_cacheInType_7148_ = crate::leanh::lean_ctor_get(v_canon_7133_, 1);
                v_isSharedCheck_7163_ = (!crate::leanh::lean_is_exclusive(v_canon_7133_)) as u8;
                if v_isSharedCheck_7163_ == 0 {
                    v___x_7150_ = v_canon_7133_;
                    v_isShared_7151_ = v_isSharedCheck_7163_;
                    state = 77;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cacheInType_7148_);
                    crate::leanh::lean_inc(v_cache_7147_);
                    crate::leanh::lean_dec(v_canon_7133_);
                    v___x_7150_ = crate::leanh::lean_box(0);
                    v_isShared_7151_ = v_isSharedCheck_7163_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                crate::leanh::lean_inc(v_a_7128_);
                v___x_7152_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_cacheInType_7148_, v_e_6645_, v_a_7128_);
                if v_isShared_7151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7150_, 1, v___x_7152_);
                    v___x_7154_ = v___x_7150_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_7162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_cache_7147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 1, v___x_7152_);
                    v___x_7154_ = v_reuseFailAlloc_7162_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_7146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7145_, 9, v___x_7154_);
                    v___x_7156_ = v___x_7145_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_7161_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 0, v_share_7134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 1, v_maxFVar_7135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 2, v_proofInstInfo_7136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 3, v_inferType_7137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 4, v_getLevel_7138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 5, v_congrInfo_7139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 6, v_defEqI_7140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 7, v_extensions_7141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 8, v_issues_7142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7161_, 9, v___x_7154_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7161_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_7143_,
                    );
                    v___x_7156_ = v_reuseFailAlloc_7161_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_7157_ = lean_st_ref_set(v_a_6648_, v___x_7156_);
                if v_isShared_7131_ == 0 {
                    v___x_7159_ = v___x_7130_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_7160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7160_, 0, v_a_7128_);
                    v___x_7159_ = v_reuseFailAlloc_7160_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                return v___x_7159_;
            }
            81 => {
                v___x_7173_ = lean_ptr_addr(v_expr_7167_);
                v___x_7174_ = lean_ptr_addr(v_a_7169_);
                v___x_7175_ = lean_usize_dec_eq(v___x_7173_, v___x_7174_);
                if v___x_7175_ == 0 {
                    crate::leanh::lean_inc(v_data_7166_);
                    crate::leanh::lean_dec_ref_known(v_e_6645_, 2);
                    v___x_7176_ = l_Lean_Expr_mdata___override(v_data_7166_, v_a_7169_);
                    if v_isShared_7172_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7171_, 0, v___x_7176_);
                        v___x_7178_ = v___x_7171_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_7179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7179_, 0, v___x_7176_);
                        v___x_7178_ = v_reuseFailAlloc_7179_;
                        state = 82;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7169_);
                    if v_isShared_7172_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7171_, 0, v_e_6645_);
                        v___x_7181_ = v___x_7171_;
                        state = 83;
                        continue;
                    } else {
                        v_reuseFailAlloc_7182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7182_, 0, v_e_6645_);
                        v___x_7181_ = v_reuseFailAlloc_7182_;
                        state = 83;
                        continue;
                    }
                }
            }
            82 => {
                return v___x_7178_;
            }
            83 => {
                return v___x_7181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(
    mut v_e_7185_: *mut crate::leanh::LeanObject,
    mut v_a_7186_: u8,
    mut v_a_7187_: *mut crate::leanh::LeanObject,
    mut v_a_7188_: *mut crate::leanh::LeanObject,
    mut v_a_7189_: *mut crate::leanh::LeanObject,
    mut v_a_7190_: *mut crate::leanh::LeanObject,
    mut v_a_7191_: *mut crate::leanh::LeanObject,
    mut v_a_7192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7196_: u8 = 0;
    let mut v___x_7197_: u8 = 0;
    let mut v___x_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7203_: u8 = 0;
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7207_: u8 = 0;
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_7186_ == 0 {
                    crate::leanh::lean_inc_ref(v_e_7185_);
                    v___x_7194_ =
                        l_Lean_Meta_isProp(v_e_7185_, v_a_7189_, v_a_7190_, v_a_7191_, v_a_7192_);
                    if crate::leanh::lean_obj_tag(v___x_7194_) == 0 {
                        v_a_7195_ = crate::leanh::lean_ctor_get(v___x_7194_, 0);
                        crate::leanh::lean_inc(v_a_7195_);
                        crate::leanh::lean_dec_ref_known(v___x_7194_, 1);
                        v___x_7196_ = (crate::leanh::lean_unbox(v_a_7195_) as u8);
                        crate::leanh::lean_dec(v_a_7195_);
                        if v___x_7196_ == 0 {
                            v___x_7197_ = 1;
                            v___x_7198_ =
                                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                    v_e_7185_,
                                    v___x_7197_,
                                    v_a_7187_,
                                    v_a_7188_,
                                    v_a_7189_,
                                    v_a_7190_,
                                    v_a_7191_,
                                    v_a_7192_,
                                );
                            return v___x_7198_;
                        } else {
                            v___x_7199_ =
                                l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                                    v_e_7185_, v_a_7186_, v_a_7187_, v_a_7188_, v_a_7189_,
                                    v_a_7190_, v_a_7191_, v_a_7192_,
                                );
                            return v___x_7199_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7185_);
                        v_a_7200_ = crate::leanh::lean_ctor_get(v___x_7194_, 0);
                        v_isSharedCheck_7207_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7194_)) as u8;
                        if v_isSharedCheck_7207_ == 0 {
                            v___x_7202_ = v___x_7194_;
                            v_isShared_7203_ = v_isSharedCheck_7207_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7200_);
                            crate::leanh::lean_dec(v___x_7194_);
                            v___x_7202_ = crate::leanh::lean_box(0);
                            v_isShared_7203_ = v_isSharedCheck_7207_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_7208_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                        v_e_7185_, v_a_7186_, v_a_7187_, v_a_7188_, v_a_7189_, v_a_7190_,
                        v_a_7191_, v_a_7192_,
                    );
                    return v___x_7208_;
                }
            }
            1 => {
                if v_isShared_7203_ == 0 {
                    v___x_7205_ = v___x_7202_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7200_);
                    v___x_7205_ = v_reuseFailAlloc_7206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed(
    mut v_fvars_7209_: *mut crate::leanh::LeanObject,
    mut v_body_7210_: *mut crate::leanh::LeanObject,
    mut v_x_7211_: *mut crate::leanh::LeanObject,
    mut v___y_7212_: *mut crate::leanh::LeanObject,
    mut v___y_7213_: *mut crate::leanh::LeanObject,
    mut v___y_7214_: *mut crate::leanh::LeanObject,
    mut v___y_7215_: *mut crate::leanh::LeanObject,
    mut v___y_7216_: *mut crate::leanh::LeanObject,
    mut v___y_7217_: *mut crate::leanh::LeanObject,
    mut v___y_7218_: *mut crate::leanh::LeanObject,
    mut v___y_7219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_64319__boxed_7220_: u8 = 0;
    let mut v_res_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_64319__boxed_7220_ = (crate::leanh::lean_unbox(v___y_7212_) as u8);
    v_res_7221_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(
        v_fvars_7209_,
        v_body_7210_,
        v_x_7211_,
        v___y_64319__boxed_7220_,
        v___y_7213_,
        v___y_7214_,
        v___y_7215_,
        v___y_7216_,
        v___y_7217_,
        v___y_7218_,
    );
    crate::leanh::lean_dec(v___y_7218_);
    crate::leanh::lean_dec_ref(v___y_7217_);
    crate::leanh::lean_dec(v___y_7216_);
    crate::leanh::lean_dec_ref(v___y_7215_);
    crate::leanh::lean_dec(v___y_7214_);
    crate::leanh::lean_dec_ref(v___y_7213_);
    return v_res_7221_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(
    mut v_fvars_7222_: *mut crate::leanh::LeanObject,
    mut v_e_7223_: *mut crate::leanh::LeanObject,
    mut v_a_7224_: u8,
    mut v_a_7225_: *mut crate::leanh::LeanObject,
    mut v_a_7226_: *mut crate::leanh::LeanObject,
    mut v_a_7227_: *mut crate::leanh::LeanObject,
    mut v_a_7228_: *mut crate::leanh::LeanObject,
    mut v_a_7229_: *mut crate::leanh::LeanObject,
    mut v_a_7230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_7223_) == 7 {
        let mut v_binderName_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7235_: u8 = 0;
        let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_7232_ = crate::leanh::lean_ctor_get(v_e_7223_, 0);
        crate::leanh::lean_inc(v_binderName_7232_);
        v_binderType_7233_ = crate::leanh::lean_ctor_get(v_e_7223_, 1);
        crate::leanh::lean_inc_ref(v_binderType_7233_);
        v_body_7234_ = crate::leanh::lean_ctor_get(v_e_7223_, 2);
        crate::leanh::lean_inc_ref(v_body_7234_);
        v_binderInfo_7235_ = crate::leanh::lean_ctor_get_uint8(
            v_e_7223_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_7223_, 3);
        v___x_7236_ = lean_expr_instantiate_rev(v_binderType_7233_, v_fvars_7222_);
        crate::leanh::lean_dec_ref(v_binderType_7233_);
        v___x_7237_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(
            v___x_7236_,
            v_a_7224_,
            v_a_7225_,
            v_a_7226_,
            v_a_7227_,
            v_a_7228_,
            v_a_7229_,
            v_a_7230_,
        );
        if crate::leanh::lean_obj_tag(v___x_7237_) == 0 {
            let mut v_a_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7240_: u8 = 0;
            let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7238_ = crate::leanh::lean_ctor_get(v___x_7237_, 0);
            crate::leanh::lean_inc(v_a_7238_);
            crate::leanh::lean_dec_ref_known(v___x_7237_, 1);
            v___f_7239_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
            crate::leanh::lean_closure_set(v___f_7239_, 0, v_fvars_7222_);
            crate::leanh::lean_closure_set(v___f_7239_, 1, v_body_7234_);
            v___x_7240_ = 0;
            v___x_7241_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_binderName_7232_, v_binderInfo_7235_, v_a_7238_, v___f_7239_, v___x_7240_, v_a_7224_, v_a_7225_, v_a_7226_, v_a_7227_, v_a_7228_, v_a_7229_, v_a_7230_);
            return v___x_7241_;
        } else {
            crate::leanh::lean_dec_ref(v_body_7234_);
            crate::leanh::lean_dec(v_binderName_7232_);
            crate::leanh::lean_dec_ref(v_fvars_7222_);
            return v___x_7237_;
        }
    } else {
        let mut v___x_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7242_ = lean_expr_instantiate_rev(v_e_7223_, v_fvars_7222_);
        crate::leanh::lean_dec_ref(v_e_7223_);
        v___x_7243_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(
            v___x_7242_,
            v_a_7224_,
            v_a_7225_,
            v_a_7226_,
            v_a_7227_,
            v_a_7228_,
            v_a_7229_,
            v_a_7230_,
        );
        if crate::leanh::lean_obj_tag(v___x_7243_) == 0 {
            let mut v_a_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7245_: u8 = 0;
            let mut v___x_7246_: u8 = 0;
            let mut v___x_7247_: u8 = 0;
            let mut v___x_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7244_ = crate::leanh::lean_ctor_get(v___x_7243_, 0);
            crate::leanh::lean_inc(v_a_7244_);
            crate::leanh::lean_dec_ref_known(v___x_7243_, 1);
            v___x_7245_ = 0;
            v___x_7246_ = 1;
            v___x_7247_ = 1;
            v___x_7248_ = l_Lean_Meta_mkForallFVars(
                v_fvars_7222_,
                v_a_7244_,
                v___x_7245_,
                v___x_7246_,
                v___x_7246_,
                v___x_7247_,
                v_a_7227_,
                v_a_7228_,
                v_a_7229_,
                v_a_7230_,
            );
            crate::leanh::lean_dec_ref(v_fvars_7222_);
            return v___x_7248_;
        } else {
            crate::leanh::lean_dec_ref(v_fvars_7222_);
            return v___x_7243_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___lam__0(
    mut v_fvars_7249_: *mut crate::leanh::LeanObject,
    mut v_body_7250_: *mut crate::leanh::LeanObject,
    mut v_x_7251_: *mut crate::leanh::LeanObject,
    mut v___y_7252_: u8,
    mut v___y_7253_: *mut crate::leanh::LeanObject,
    mut v___y_7254_: *mut crate::leanh::LeanObject,
    mut v___y_7255_: *mut crate::leanh::LeanObject,
    mut v___y_7256_: *mut crate::leanh::LeanObject,
    mut v___y_7257_: *mut crate::leanh::LeanObject,
    mut v___y_7258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7260_ = lean_array_push(v_fvars_7249_, v_x_7251_);
    v___x_7261_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(
        v___x_7260_,
        v_body_7250_,
        v___y_7252_,
        v___y_7253_,
        v___y_7254_,
        v___y_7255_,
        v___y_7256_,
        v___y_7257_,
        v___y_7258_,
    );
    return v___x_7261_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost___boxed(
    mut v_e_7262_: *mut crate::leanh::LeanObject,
    mut v_a_7263_: *mut crate::leanh::LeanObject,
    mut v_a_7264_: *mut crate::leanh::LeanObject,
    mut v_a_7265_: *mut crate::leanh::LeanObject,
    mut v_a_7266_: *mut crate::leanh::LeanObject,
    mut v_a_7267_: *mut crate::leanh::LeanObject,
    mut v_a_7268_: *mut crate::leanh::LeanObject,
    mut v_a_7269_: *mut crate::leanh::LeanObject,
    mut v_a_7270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7271_: u8 = 0;
    let mut v_res_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7271_ = (crate::leanh::lean_unbox(v_a_7263_) as u8);
    v_res_7272_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppAndPost(
        v_e_7262_,
        v_a_boxed_7271_,
        v_a_7264_,
        v_a_7265_,
        v_a_7266_,
        v_a_7267_,
        v_a_7268_,
        v_a_7269_,
    );
    crate::leanh::lean_dec(v_a_7269_);
    crate::leanh::lean_dec_ref(v_a_7268_);
    crate::leanh::lean_dec(v_a_7267_);
    crate::leanh::lean_dec_ref(v_a_7266_);
    crate::leanh::lean_dec(v_a_7265_);
    crate::leanh::lean_dec_ref(v_a_7264_);
    return v_res_7272_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27___boxed(
    mut v_e_7273_: *mut crate::leanh::LeanObject,
    mut v_a_7274_: *mut crate::leanh::LeanObject,
    mut v_a_7275_: *mut crate::leanh::LeanObject,
    mut v_a_7276_: *mut crate::leanh::LeanObject,
    mut v_a_7277_: *mut crate::leanh::LeanObject,
    mut v_a_7278_: *mut crate::leanh::LeanObject,
    mut v_a_7279_: *mut crate::leanh::LeanObject,
    mut v_a_7280_: *mut crate::leanh::LeanObject,
    mut v_a_7281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7282_: u8 = 0;
    let mut v_res_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7282_ = (crate::leanh::lean_unbox(v_a_7274_) as u8);
    v_res_7283_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType_x27(
        v_e_7273_,
        v_a_boxed_7282_,
        v_a_7275_,
        v_a_7276_,
        v_a_7277_,
        v_a_7278_,
        v_a_7279_,
        v_a_7280_,
    );
    crate::leanh::lean_dec(v_a_7280_);
    crate::leanh::lean_dec_ref(v_a_7279_);
    crate::leanh::lean_dec(v_a_7278_);
    crate::leanh::lean_dec_ref(v_a_7277_);
    crate::leanh::lean_dec(v_a_7276_);
    crate::leanh::lean_dec_ref(v_a_7275_);
    return v_res_7283_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault___boxed(
    mut v_e_7284_: *mut crate::leanh::LeanObject,
    mut v_a_7285_: *mut crate::leanh::LeanObject,
    mut v_a_7286_: *mut crate::leanh::LeanObject,
    mut v_a_7287_: *mut crate::leanh::LeanObject,
    mut v_a_7288_: *mut crate::leanh::LeanObject,
    mut v_a_7289_: *mut crate::leanh::LeanObject,
    mut v_a_7290_: *mut crate::leanh::LeanObject,
    mut v_a_7291_: *mut crate::leanh::LeanObject,
    mut v_a_7292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7293_: u8 = 0;
    let mut v_res_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7293_ = (crate::leanh::lean_unbox(v_a_7285_) as u8);
    v_res_7294_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault(
        v_e_7284_,
        v_a_boxed_7293_,
        v_a_7286_,
        v_a_7287_,
        v_a_7288_,
        v_a_7289_,
        v_a_7290_,
        v_a_7291_,
    );
    crate::leanh::lean_dec(v_a_7291_);
    crate::leanh::lean_dec_ref(v_a_7290_);
    crate::leanh::lean_dec(v_a_7289_);
    crate::leanh::lean_dec_ref(v_a_7288_);
    crate::leanh::lean_dec(v_a_7287_);
    crate::leanh::lean_dec_ref(v_a_7286_);
    return v_res_7294_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27___boxed(
    mut v_e_7295_: *mut crate::leanh::LeanObject,
    mut v_report_7296_: *mut crate::leanh::LeanObject,
    mut v_a_7297_: *mut crate::leanh::LeanObject,
    mut v_a_7298_: *mut crate::leanh::LeanObject,
    mut v_a_7299_: *mut crate::leanh::LeanObject,
    mut v_a_7300_: *mut crate::leanh::LeanObject,
    mut v_a_7301_: *mut crate::leanh::LeanObject,
    mut v_a_7302_: *mut crate::leanh::LeanObject,
    mut v_a_7303_: *mut crate::leanh::LeanObject,
    mut v_a_7304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_report_boxed_7305_: u8 = 0;
    let mut v_a_boxed_7306_: u8 = 0;
    let mut v_res_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_report_boxed_7305_ = (crate::leanh::lean_unbox(v_report_7296_) as u8);
    v_a_boxed_7306_ = (crate::leanh::lean_unbox(v_a_7297_) as u8);
    v_res_7307_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst_x27(
        v_e_7295_,
        v_report_boxed_7305_,
        v_a_boxed_7306_,
        v_a_7298_,
        v_a_7299_,
        v_a_7300_,
        v_a_7301_,
        v_a_7302_,
        v_a_7303_,
    );
    crate::leanh::lean_dec(v_a_7303_);
    crate::leanh::lean_dec_ref(v_a_7302_);
    crate::leanh::lean_dec(v_a_7301_);
    crate::leanh::lean_dec_ref(v_a_7300_);
    crate::leanh::lean_dec(v_a_7299_);
    crate::leanh::lean_dec_ref(v_a_7298_);
    return v_res_7307_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda___boxed(
    mut v_e_7308_: *mut crate::leanh::LeanObject,
    mut v_a_7309_: *mut crate::leanh::LeanObject,
    mut v_a_7310_: *mut crate::leanh::LeanObject,
    mut v_a_7311_: *mut crate::leanh::LeanObject,
    mut v_a_7312_: *mut crate::leanh::LeanObject,
    mut v_a_7313_: *mut crate::leanh::LeanObject,
    mut v_a_7314_: *mut crate::leanh::LeanObject,
    mut v_a_7315_: *mut crate::leanh::LeanObject,
    mut v_a_7316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7317_: u8 = 0;
    let mut v_res_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7317_ = (crate::leanh::lean_unbox(v_a_7309_) as u8);
    v_res_7318_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambda(
        v_e_7308_,
        v_a_boxed_7317_,
        v_a_7310_,
        v_a_7311_,
        v_a_7312_,
        v_a_7313_,
        v_a_7314_,
        v_a_7315_,
    );
    crate::leanh::lean_dec(v_a_7315_);
    crate::leanh::lean_dec_ref(v_a_7314_);
    crate::leanh::lean_dec(v_a_7313_);
    crate::leanh::lean_dec_ref(v_a_7312_);
    crate::leanh::lean_dec(v_a_7311_);
    crate::leanh::lean_dec_ref(v_a_7310_);
    return v_res_7318_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType___boxed(
    mut v_e_7319_: *mut crate::leanh::LeanObject,
    mut v_a_7320_: *mut crate::leanh::LeanObject,
    mut v_a_7321_: *mut crate::leanh::LeanObject,
    mut v_a_7322_: *mut crate::leanh::LeanObject,
    mut v_a_7323_: *mut crate::leanh::LeanObject,
    mut v_a_7324_: *mut crate::leanh::LeanObject,
    mut v_a_7325_: *mut crate::leanh::LeanObject,
    mut v_a_7326_: *mut crate::leanh::LeanObject,
    mut v_a_7327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7328_: u8 = 0;
    let mut v_res_7329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7328_ = (crate::leanh::lean_unbox(v_a_7320_) as u8);
    v_res_7329_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInsideType(
        v_e_7319_,
        v_a_boxed_7328_,
        v_a_7321_,
        v_a_7322_,
        v_a_7323_,
        v_a_7324_,
        v_a_7325_,
        v_a_7326_,
    );
    crate::leanh::lean_dec(v_a_7326_);
    crate::leanh::lean_dec_ref(v_a_7325_);
    crate::leanh::lean_dec(v_a_7324_);
    crate::leanh::lean_dec_ref(v_a_7323_);
    crate::leanh::lean_dec(v_a_7322_);
    crate::leanh::lean_dec_ref(v_a_7321_);
    return v_res_7329_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall___boxed(
    mut v_fvars_7330_: *mut crate::leanh::LeanObject,
    mut v_e_7331_: *mut crate::leanh::LeanObject,
    mut v_a_7332_: *mut crate::leanh::LeanObject,
    mut v_a_7333_: *mut crate::leanh::LeanObject,
    mut v_a_7334_: *mut crate::leanh::LeanObject,
    mut v_a_7335_: *mut crate::leanh::LeanObject,
    mut v_a_7336_: *mut crate::leanh::LeanObject,
    mut v_a_7337_: *mut crate::leanh::LeanObject,
    mut v_a_7338_: *mut crate::leanh::LeanObject,
    mut v_a_7339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7340_: u8 = 0;
    let mut v_res_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7340_ = (crate::leanh::lean_unbox(v_a_7332_) as u8);
    v_res_7341_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonForall(
        v_fvars_7330_,
        v_e_7331_,
        v_a_boxed_7340_,
        v_a_7333_,
        v_a_7334_,
        v_a_7335_,
        v_a_7336_,
        v_a_7337_,
        v_a_7338_,
    );
    crate::leanh::lean_dec(v_a_7338_);
    crate::leanh::lean_dec_ref(v_a_7337_);
    crate::leanh::lean_dec(v_a_7336_);
    crate::leanh::lean_dec_ref(v_a_7335_);
    crate::leanh::lean_dec(v_a_7334_);
    crate::leanh::lean_dec_ref(v_a_7333_);
    return v_res_7341_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop___boxed(
    mut v_fvars_7342_: *mut crate::leanh::LeanObject,
    mut v_e_7343_: *mut crate::leanh::LeanObject,
    mut v_a_7344_: *mut crate::leanh::LeanObject,
    mut v_a_7345_: *mut crate::leanh::LeanObject,
    mut v_a_7346_: *mut crate::leanh::LeanObject,
    mut v_a_7347_: *mut crate::leanh::LeanObject,
    mut v_a_7348_: *mut crate::leanh::LeanObject,
    mut v_a_7349_: *mut crate::leanh::LeanObject,
    mut v_a_7350_: *mut crate::leanh::LeanObject,
    mut v_a_7351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7352_: u8 = 0;
    let mut v_res_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7352_ = (crate::leanh::lean_unbox(v_a_7344_) as u8);
    v_res_7353_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop(
        v_fvars_7342_,
        v_e_7343_,
        v_a_boxed_7352_,
        v_a_7345_,
        v_a_7346_,
        v_a_7347_,
        v_a_7348_,
        v_a_7349_,
        v_a_7350_,
    );
    crate::leanh::lean_dec(v_a_7350_);
    crate::leanh::lean_dec_ref(v_a_7349_);
    crate::leanh::lean_dec(v_a_7348_);
    crate::leanh::lean_dec_ref(v_a_7347_);
    crate::leanh::lean_dec(v_a_7346_);
    crate::leanh::lean_dec_ref(v_a_7345_);
    return v_res_7353_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch___boxed(
    mut v_e_7354_: *mut crate::leanh::LeanObject,
    mut v_a_7355_: *mut crate::leanh::LeanObject,
    mut v_a_7356_: *mut crate::leanh::LeanObject,
    mut v_a_7357_: *mut crate::leanh::LeanObject,
    mut v_a_7358_: *mut crate::leanh::LeanObject,
    mut v_a_7359_: *mut crate::leanh::LeanObject,
    mut v_a_7360_: *mut crate::leanh::LeanObject,
    mut v_a_7361_: *mut crate::leanh::LeanObject,
    mut v_a_7362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7363_: u8 = 0;
    let mut v_res_7364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7363_ = (crate::leanh::lean_unbox(v_a_7355_) as u8);
    v_res_7364_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonMatch(
        v_e_7354_,
        v_a_boxed_7363_,
        v_a_7356_,
        v_a_7357_,
        v_a_7358_,
        v_a_7359_,
        v_a_7360_,
        v_a_7361_,
    );
    crate::leanh::lean_dec(v_a_7361_);
    crate::leanh::lean_dec_ref(v_a_7360_);
    crate::leanh::lean_dec(v_a_7359_);
    crate::leanh::lean_dec_ref(v_a_7358_);
    crate::leanh::lean_dec(v_a_7357_);
    crate::leanh::lean_dec_ref(v_a_7356_);
    return v_res_7364_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet___boxed(
    mut v_fvars_7365_: *mut crate::leanh::LeanObject,
    mut v_e_7366_: *mut crate::leanh::LeanObject,
    mut v_a_7367_: *mut crate::leanh::LeanObject,
    mut v_a_7368_: *mut crate::leanh::LeanObject,
    mut v_a_7369_: *mut crate::leanh::LeanObject,
    mut v_a_7370_: *mut crate::leanh::LeanObject,
    mut v_a_7371_: *mut crate::leanh::LeanObject,
    mut v_a_7372_: *mut crate::leanh::LeanObject,
    mut v_a_7373_: *mut crate::leanh::LeanObject,
    mut v_a_7374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7375_: u8 = 0;
    let mut v_res_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7375_ = (crate::leanh::lean_unbox(v_a_7367_) as u8);
    v_res_7376_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet(
        v_fvars_7365_,
        v_e_7366_,
        v_a_boxed_7375_,
        v_a_7368_,
        v_a_7369_,
        v_a_7370_,
        v_a_7371_,
        v_a_7372_,
        v_a_7373_,
    );
    crate::leanh::lean_dec(v_a_7373_);
    crate::leanh::lean_dec_ref(v_a_7372_);
    crate::leanh::lean_dec(v_a_7371_);
    crate::leanh::lean_dec_ref(v_a_7370_);
    crate::leanh::lean_dec(v_a_7369_);
    crate::leanh::lean_dec_ref(v_a_7368_);
    return v_res_7376_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond___boxed(
    mut v_f_7377_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7378_: *mut crate::leanh::LeanObject,
    mut v_c_7379_: *mut crate::leanh::LeanObject,
    mut v_a_7380_: *mut crate::leanh::LeanObject,
    mut v_b_7381_: *mut crate::leanh::LeanObject,
    mut v_a_7382_: *mut crate::leanh::LeanObject,
    mut v_a_7383_: *mut crate::leanh::LeanObject,
    mut v_a_7384_: *mut crate::leanh::LeanObject,
    mut v_a_7385_: *mut crate::leanh::LeanObject,
    mut v_a_7386_: *mut crate::leanh::LeanObject,
    mut v_a_7387_: *mut crate::leanh::LeanObject,
    mut v_a_7388_: *mut crate::leanh::LeanObject,
    mut v_a_7389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7390_: u8 = 0;
    let mut v_res_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7390_ = (crate::leanh::lean_unbox(v_a_7382_) as u8);
    v_res_7391_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonCond(
        v_f_7377_,
        v_00_u03b1_7378_,
        v_c_7379_,
        v_a_7380_,
        v_b_7381_,
        v_a_boxed_7390_,
        v_a_7383_,
        v_a_7384_,
        v_a_7385_,
        v_a_7386_,
        v_a_7387_,
        v_a_7388_,
    );
    crate::leanh::lean_dec(v_a_7388_);
    crate::leanh::lean_dec_ref(v_a_7387_);
    crate::leanh::lean_dec(v_a_7386_);
    crate::leanh::lean_dec_ref(v_a_7385_);
    crate::leanh::lean_dec(v_a_7384_);
    crate::leanh::lean_dec_ref(v_a_7383_);
    return v_res_7391_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte___boxed(
    mut v_f_7392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7393_: *mut crate::leanh::LeanObject,
    mut v_c_7394_: *mut crate::leanh::LeanObject,
    mut v_inst_7395_: *mut crate::leanh::LeanObject,
    mut v_a_7396_: *mut crate::leanh::LeanObject,
    mut v_b_7397_: *mut crate::leanh::LeanObject,
    mut v_a_7398_: *mut crate::leanh::LeanObject,
    mut v_a_7399_: *mut crate::leanh::LeanObject,
    mut v_a_7400_: *mut crate::leanh::LeanObject,
    mut v_a_7401_: *mut crate::leanh::LeanObject,
    mut v_a_7402_: *mut crate::leanh::LeanObject,
    mut v_a_7403_: *mut crate::leanh::LeanObject,
    mut v_a_7404_: *mut crate::leanh::LeanObject,
    mut v_a_7405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7406_: u8 = 0;
    let mut v_res_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7406_ = (crate::leanh::lean_unbox(v_a_7398_) as u8);
    v_res_7407_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonIte(
        v_f_7392_,
        v_00_u03b1_7393_,
        v_c_7394_,
        v_inst_7395_,
        v_a_7396_,
        v_b_7397_,
        v_a_boxed_7406_,
        v_a_7399_,
        v_a_7400_,
        v_a_7401_,
        v_a_7402_,
        v_a_7403_,
        v_a_7404_,
    );
    crate::leanh::lean_dec(v_a_7404_);
    crate::leanh::lean_dec_ref(v_a_7403_);
    crate::leanh::lean_dec(v_a_7402_);
    crate::leanh::lean_dec_ref(v_a_7401_);
    crate::leanh::lean_dec(v_a_7400_);
    crate::leanh::lean_dec_ref(v_a_7399_);
    return v_res_7407_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore___boxed(
    mut v_e_7408_: *mut crate::leanh::LeanObject,
    mut v_a_7409_: *mut crate::leanh::LeanObject,
    mut v_a_7410_: *mut crate::leanh::LeanObject,
    mut v_a_7411_: *mut crate::leanh::LeanObject,
    mut v_a_7412_: *mut crate::leanh::LeanObject,
    mut v_a_7413_: *mut crate::leanh::LeanObject,
    mut v_a_7414_: *mut crate::leanh::LeanObject,
    mut v_a_7415_: *mut crate::leanh::LeanObject,
    mut v_a_7416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7417_: u8 = 0;
    let mut v_res_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7417_ = (crate::leanh::lean_unbox(v_a_7409_) as u8);
    v_res_7418_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDecCore(
        v_e_7408_,
        v_a_boxed_7417_,
        v_a_7410_,
        v_a_7411_,
        v_a_7412_,
        v_a_7413_,
        v_a_7414_,
        v_a_7415_,
    );
    crate::leanh::lean_dec(v_a_7415_);
    crate::leanh::lean_dec_ref(v_a_7414_);
    crate::leanh::lean_dec(v_a_7413_);
    crate::leanh::lean_dec_ref(v_a_7412_);
    crate::leanh::lean_dec(v_a_7411_);
    crate::leanh::lean_dec_ref(v_a_7410_);
    return v_res_7418_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj___boxed(
    mut v_e_7419_: *mut crate::leanh::LeanObject,
    mut v_a_7420_: *mut crate::leanh::LeanObject,
    mut v_a_7421_: *mut crate::leanh::LeanObject,
    mut v_a_7422_: *mut crate::leanh::LeanObject,
    mut v_a_7423_: *mut crate::leanh::LeanObject,
    mut v_a_7424_: *mut crate::leanh::LeanObject,
    mut v_a_7425_: *mut crate::leanh::LeanObject,
    mut v_a_7426_: *mut crate::leanh::LeanObject,
    mut v_a_7427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7428_: u8 = 0;
    let mut v_res_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7428_ = (crate::leanh::lean_unbox(v_a_7420_) as u8);
    v_res_7429_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonProj(
        v_e_7419_,
        v_a_boxed_7428_,
        v_a_7421_,
        v_a_7422_,
        v_a_7423_,
        v_a_7424_,
        v_a_7425_,
        v_a_7426_,
    );
    crate::leanh::lean_dec(v_a_7426_);
    crate::leanh::lean_dec_ref(v_a_7425_);
    crate::leanh::lean_dec(v_a_7424_);
    crate::leanh::lean_dec_ref(v_a_7423_);
    crate::leanh::lean_dec(v_a_7422_);
    crate::leanh::lean_dec_ref(v_a_7421_);
    return v_res_7429_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27___boxed(
    mut v_g_7430_: *mut crate::leanh::LeanObject,
    mut v_prop_7431_: *mut crate::leanh::LeanObject,
    mut v_inst_7432_: *mut crate::leanh::LeanObject,
    mut v_e_7433_: *mut crate::leanh::LeanObject,
    mut v_a_7434_: *mut crate::leanh::LeanObject,
    mut v_a_7435_: *mut crate::leanh::LeanObject,
    mut v_a_7436_: *mut crate::leanh::LeanObject,
    mut v_a_7437_: *mut crate::leanh::LeanObject,
    mut v_a_7438_: *mut crate::leanh::LeanObject,
    mut v_a_7439_: *mut crate::leanh::LeanObject,
    mut v_a_7440_: *mut crate::leanh::LeanObject,
    mut v_a_7441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7442_: u8 = 0;
    let mut v_res_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7442_ = (crate::leanh::lean_unbox(v_a_7434_) as u8);
    v_res_7443_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec_x27(
        v_g_7430_,
        v_prop_7431_,
        v_inst_7432_,
        v_e_7433_,
        v_a_boxed_7442_,
        v_a_7435_,
        v_a_7436_,
        v_a_7437_,
        v_a_7438_,
        v_a_7439_,
        v_a_7440_,
    );
    crate::leanh::lean_dec(v_a_7440_);
    crate::leanh::lean_dec_ref(v_a_7439_);
    crate::leanh::lean_dec(v_a_7438_);
    crate::leanh::lean_dec_ref(v_a_7437_);
    crate::leanh::lean_dec(v_a_7436_);
    crate::leanh::lean_dec_ref(v_a_7435_);
    return v_res_7443_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst___boxed(
    mut v_e_7444_: *mut crate::leanh::LeanObject,
    mut v_report_7445_: *mut crate::leanh::LeanObject,
    mut v_a_7446_: *mut crate::leanh::LeanObject,
    mut v_a_7447_: *mut crate::leanh::LeanObject,
    mut v_a_7448_: *mut crate::leanh::LeanObject,
    mut v_a_7449_: *mut crate::leanh::LeanObject,
    mut v_a_7450_: *mut crate::leanh::LeanObject,
    mut v_a_7451_: *mut crate::leanh::LeanObject,
    mut v_a_7452_: *mut crate::leanh::LeanObject,
    mut v_a_7453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_report_boxed_7454_: u8 = 0;
    let mut v_a_boxed_7455_: u8 = 0;
    let mut v_res_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_report_boxed_7454_ = (crate::leanh::lean_unbox(v_report_7445_) as u8);
    v_a_boxed_7455_ = (crate::leanh::lean_unbox(v_a_7446_) as u8);
    v_res_7456_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInst(
        v_e_7444_,
        v_report_boxed_7454_,
        v_a_boxed_7455_,
        v_a_7447_,
        v_a_7448_,
        v_a_7449_,
        v_a_7450_,
        v_a_7451_,
        v_a_7452_,
    );
    crate::leanh::lean_dec(v_a_7452_);
    crate::leanh::lean_dec_ref(v_a_7451_);
    crate::leanh::lean_dec(v_a_7450_);
    crate::leanh::lean_dec_ref(v_a_7449_);
    crate::leanh::lean_dec(v_a_7448_);
    crate::leanh::lean_dec_ref(v_a_7447_);
    return v_res_7456_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec___boxed(
    mut v_g_7457_: *mut crate::leanh::LeanObject,
    mut v_prop_7458_: *mut crate::leanh::LeanObject,
    mut v_h_7459_: *mut crate::leanh::LeanObject,
    mut v_e_7460_: *mut crate::leanh::LeanObject,
    mut v_a_7461_: *mut crate::leanh::LeanObject,
    mut v_a_7462_: *mut crate::leanh::LeanObject,
    mut v_a_7463_: *mut crate::leanh::LeanObject,
    mut v_a_7464_: *mut crate::leanh::LeanObject,
    mut v_a_7465_: *mut crate::leanh::LeanObject,
    mut v_a_7466_: *mut crate::leanh::LeanObject,
    mut v_a_7467_: *mut crate::leanh::LeanObject,
    mut v_a_7468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7469_: u8 = 0;
    let mut v_res_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7469_ = (crate::leanh::lean_unbox(v_a_7461_) as u8);
    v_res_7470_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstDec(
        v_g_7457_,
        v_prop_7458_,
        v_h_7459_,
        v_e_7460_,
        v_a_boxed_7469_,
        v_a_7462_,
        v_a_7463_,
        v_a_7464_,
        v_a_7465_,
        v_a_7466_,
        v_a_7467_,
    );
    crate::leanh::lean_dec(v_a_7467_);
    crate::leanh::lean_dec_ref(v_a_7466_);
    crate::leanh::lean_dec(v_a_7465_);
    crate::leanh::lean_dec_ref(v_a_7464_);
    crate::leanh::lean_dec(v_a_7463_);
    crate::leanh::lean_dec_ref(v_a_7462_);
    return v_res_7470_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp___boxed(
    mut v_e_7471_: *mut crate::leanh::LeanObject,
    mut v_a_7472_: *mut crate::leanh::LeanObject,
    mut v_a_7473_: *mut crate::leanh::LeanObject,
    mut v_a_7474_: *mut crate::leanh::LeanObject,
    mut v_a_7475_: *mut crate::leanh::LeanObject,
    mut v_a_7476_: *mut crate::leanh::LeanObject,
    mut v_a_7477_: *mut crate::leanh::LeanObject,
    mut v_a_7478_: *mut crate::leanh::LeanObject,
    mut v_a_7479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7480_: u8 = 0;
    let mut v_res_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7480_ = (crate::leanh::lean_unbox(v_a_7472_) as u8);
    v_res_7481_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp(
        v_e_7471_,
        v_a_boxed_7480_,
        v_a_7473_,
        v_a_7474_,
        v_a_7475_,
        v_a_7476_,
        v_a_7477_,
        v_a_7478_,
    );
    crate::leanh::lean_dec(v_a_7478_);
    crate::leanh::lean_dec_ref(v_a_7477_);
    crate::leanh::lean_dec(v_a_7476_);
    crate::leanh::lean_dec_ref(v_a_7475_);
    crate::leanh::lean_dec(v_a_7474_);
    crate::leanh::lean_dec_ref(v_a_7473_);
    return v_res_7481_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0___boxed(
    mut v___x_7482_: *mut crate::leanh::LeanObject,
    mut v_a_7483_: *mut crate::leanh::LeanObject,
    mut v___x_7484_: *mut crate::leanh::LeanObject,
    mut v_snd_7485_: *mut crate::leanh::LeanObject,
    mut v___x_7486_: *mut crate::leanh::LeanObject,
    mut v_fst_7487_: *mut crate::leanh::LeanObject,
    mut v_____r_7488_: *mut crate::leanh::LeanObject,
    mut v___y_7489_: *mut crate::leanh::LeanObject,
    mut v___y_7490_: *mut crate::leanh::LeanObject,
    mut v___y_7491_: *mut crate::leanh::LeanObject,
    mut v___y_7492_: *mut crate::leanh::LeanObject,
    mut v___y_7493_: *mut crate::leanh::LeanObject,
    mut v___y_7494_: *mut crate::leanh::LeanObject,
    mut v___y_7495_: *mut crate::leanh::LeanObject,
    mut v___y_7496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_64726__boxed_7497_: u8 = 0;
    let mut v___y_64728__boxed_7498_: u8 = 0;
    let mut v_res_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_64726__boxed_7497_ = (crate::leanh::lean_unbox(v___x_7486_) as u8);
    v___y_64728__boxed_7498_ = (crate::leanh::lean_unbox(v___y_7489_) as u8);
    v_res_7499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___lam__0(v___x_7482_, v_a_7483_, v___x_7484_, v_snd_7485_, v___x_64726__boxed_7497_, v_fst_7487_, v_____r_7488_, v___y_64728__boxed_7498_, v___y_7490_, v___y_7491_, v___y_7492_, v___y_7493_, v___y_7494_, v___y_7495_);
    crate::leanh::lean_dec(v___y_7495_);
    crate::leanh::lean_dec_ref(v___y_7494_);
    crate::leanh::lean_dec(v___y_7493_);
    crate::leanh::lean_dec_ref(v___y_7492_);
    crate::leanh::lean_dec(v___y_7491_);
    crate::leanh::lean_dec_ref(v___y_7490_);
    crate::leanh::lean_dec(v_a_7483_);
    crate::leanh::lean_dec_ref(v___x_7482_);
    return v_res_7499_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg___boxed(
    mut v_upperBound_7500_: *mut crate::leanh::LeanObject,
    mut v___x_7501_: *mut crate::leanh::LeanObject,
    mut v_a_7502_: *mut crate::leanh::LeanObject,
    mut v_b_7503_: *mut crate::leanh::LeanObject,
    mut v___y_7504_: *mut crate::leanh::LeanObject,
    mut v___y_7505_: *mut crate::leanh::LeanObject,
    mut v___y_7506_: *mut crate::leanh::LeanObject,
    mut v___y_7507_: *mut crate::leanh::LeanObject,
    mut v___y_7508_: *mut crate::leanh::LeanObject,
    mut v___y_7509_: *mut crate::leanh::LeanObject,
    mut v___y_7510_: *mut crate::leanh::LeanObject,
    mut v___y_7511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_64811__boxed_7512_: u8 = 0;
    let mut v_res_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_64811__boxed_7512_ = (crate::leanh::lean_unbox(v___y_7504_) as u8);
    v_res_7513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_7500_, v___x_7501_, v_a_7502_, v_b_7503_, v___y_64811__boxed_7512_, v___y_7505_, v___y_7506_, v___y_7507_, v___y_7508_, v___y_7509_, v___y_7510_);
    crate::leanh::lean_dec(v___y_7510_);
    crate::leanh::lean_dec_ref(v___y_7509_);
    crate::leanh::lean_dec(v___y_7508_);
    crate::leanh::lean_dec_ref(v___y_7507_);
    crate::leanh::lean_dec(v___y_7506_);
    crate::leanh::lean_dec_ref(v___y_7505_);
    crate::leanh::lean_dec_ref(v___x_7501_);
    crate::leanh::lean_dec(v_upperBound_7500_);
    return v_res_7513_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp___boxed(
    mut v_g_7514_: *mut crate::leanh::LeanObject,
    mut v_prop_7515_: *mut crate::leanh::LeanObject,
    mut v_h_7516_: *mut crate::leanh::LeanObject,
    mut v_e_7517_: *mut crate::leanh::LeanObject,
    mut v_a_7518_: *mut crate::leanh::LeanObject,
    mut v_a_7519_: *mut crate::leanh::LeanObject,
    mut v_a_7520_: *mut crate::leanh::LeanObject,
    mut v_a_7521_: *mut crate::leanh::LeanObject,
    mut v_a_7522_: *mut crate::leanh::LeanObject,
    mut v_a_7523_: *mut crate::leanh::LeanObject,
    mut v_a_7524_: *mut crate::leanh::LeanObject,
    mut v_a_7525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7526_: u8 = 0;
    let mut v_res_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7526_ = (crate::leanh::lean_unbox(v_a_7518_) as u8);
    v_res_7527_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonInstProp(
        v_g_7514_,
        v_prop_7515_,
        v_h_7516_,
        v_e_7517_,
        v_a_boxed_7526_,
        v_a_7519_,
        v_a_7520_,
        v_a_7521_,
        v_a_7522_,
        v_a_7523_,
        v_a_7524_,
    );
    crate::leanh::lean_dec(v_a_7524_);
    crate::leanh::lean_dec_ref(v_a_7523_);
    crate::leanh::lean_dec(v_a_7522_);
    crate::leanh::lean_dec_ref(v_a_7521_);
    crate::leanh::lean_dec(v_a_7520_);
    crate::leanh::lean_dec_ref(v_a_7519_);
    return v_res_7527_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11___boxed(
    mut v_e_7528_: *mut crate::leanh::LeanObject,
    mut v_x_7529_: *mut crate::leanh::LeanObject,
    mut v_x_7530_: *mut crate::leanh::LeanObject,
    mut v_x_7531_: *mut crate::leanh::LeanObject,
    mut v___y_7532_: *mut crate::leanh::LeanObject,
    mut v___y_7533_: *mut crate::leanh::LeanObject,
    mut v___y_7534_: *mut crate::leanh::LeanObject,
    mut v___y_7535_: *mut crate::leanh::LeanObject,
    mut v___y_7536_: *mut crate::leanh::LeanObject,
    mut v___y_7537_: *mut crate::leanh::LeanObject,
    mut v___y_7538_: *mut crate::leanh::LeanObject,
    mut v___y_7539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_64921__boxed_7540_: u8 = 0;
    let mut v_res_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_64921__boxed_7540_ = (crate::leanh::lean_unbox(v___y_7532_) as u8);
    v_res_7541_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__11(v_e_7528_, v_x_7529_, v_x_7530_, v_x_7531_, v___y_64921__boxed_7540_, v___y_7533_, v___y_7534_, v___y_7535_, v___y_7536_, v___y_7537_, v___y_7538_);
    crate::leanh::lean_dec(v___y_7538_);
    crate::leanh::lean_dec_ref(v___y_7537_);
    crate::leanh::lean_dec(v___y_7536_);
    crate::leanh::lean_dec_ref(v___y_7535_);
    crate::leanh::lean_dec(v___y_7534_);
    crate::leanh::lean_dec_ref(v___y_7533_);
    return v_res_7541_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon___boxed(
    mut v_e_7542_: *mut crate::leanh::LeanObject,
    mut v_a_7543_: *mut crate::leanh::LeanObject,
    mut v_a_7544_: *mut crate::leanh::LeanObject,
    mut v_a_7545_: *mut crate::leanh::LeanObject,
    mut v_a_7546_: *mut crate::leanh::LeanObject,
    mut v_a_7547_: *mut crate::leanh::LeanObject,
    mut v_a_7548_: *mut crate::leanh::LeanObject,
    mut v_a_7549_: *mut crate::leanh::LeanObject,
    mut v_a_7550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_7551_: u8 = 0;
    let mut v_res_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_7551_ = (crate::leanh::lean_unbox(v_a_7543_) as u8);
    v_res_7552_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
        v_e_7542_,
        v_a_boxed_7551_,
        v_a_7544_,
        v_a_7545_,
        v_a_7546_,
        v_a_7547_,
        v_a_7548_,
        v_a_7549_,
    );
    crate::leanh::lean_dec(v_a_7549_);
    crate::leanh::lean_dec_ref(v_a_7548_);
    crate::leanh::lean_dec(v_a_7547_);
    crate::leanh::lean_dec_ref(v_a_7546_);
    crate::leanh::lean_dec(v_a_7545_);
    crate::leanh::lean_dec_ref(v_a_7544_);
    return v_res_7552_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(
    mut v_declName_7553_: *mut crate::leanh::LeanObject,
    mut v___y_7554_: u8,
    mut v___y_7555_: *mut crate::leanh::LeanObject,
    mut v___y_7556_: *mut crate::leanh::LeanObject,
    mut v___y_7557_: *mut crate::leanh::LeanObject,
    mut v___y_7558_: *mut crate::leanh::LeanObject,
    mut v___y_7559_: *mut crate::leanh::LeanObject,
    mut v___y_7560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7562_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___redArg(v_declName_7553_, v___y_7560_);
    return v___x_7562_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6___boxed(
    mut v_declName_7563_: *mut crate::leanh::LeanObject,
    mut v___y_7564_: *mut crate::leanh::LeanObject,
    mut v___y_7565_: *mut crate::leanh::LeanObject,
    mut v___y_7566_: *mut crate::leanh::LeanObject,
    mut v___y_7567_: *mut crate::leanh::LeanObject,
    mut v___y_7568_: *mut crate::leanh::LeanObject,
    mut v___y_7569_: *mut crate::leanh::LeanObject,
    mut v___y_7570_: *mut crate::leanh::LeanObject,
    mut v___y_7571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_67209__boxed_7572_: u8 = 0;
    let mut v_res_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_67209__boxed_7572_ = (crate::leanh::lean_unbox(v___y_7564_) as u8);
    v_res_7573_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonApp_spec__6(v_declName_7563_, v___y_67209__boxed_7572_, v___y_7565_, v___y_7566_, v___y_7567_, v___y_7568_, v___y_7569_, v___y_7570_);
    crate::leanh::lean_dec(v___y_7570_);
    crate::leanh::lean_dec_ref(v___y_7569_);
    crate::leanh::lean_dec(v___y_7568_);
    crate::leanh::lean_dec_ref(v___y_7567_);
    crate::leanh::lean_dec(v___y_7566_);
    crate::leanh::lean_dec_ref(v___y_7565_);
    return v_res_7573_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(
    mut v_00_u03b1_7574_: *mut crate::leanh::LeanObject,
    mut v_name_7575_: *mut crate::leanh::LeanObject,
    mut v_type_7576_: *mut crate::leanh::LeanObject,
    mut v_val_7577_: *mut crate::leanh::LeanObject,
    mut v_k_7578_: *mut crate::leanh::LeanObject,
    mut v_nondep_7579_: u8,
    mut v_kind_7580_: u8,
    mut v___y_7581_: u8,
    mut v___y_7582_: *mut crate::leanh::LeanObject,
    mut v___y_7583_: *mut crate::leanh::LeanObject,
    mut v___y_7584_: *mut crate::leanh::LeanObject,
    mut v___y_7585_: *mut crate::leanh::LeanObject,
    mut v___y_7586_: *mut crate::leanh::LeanObject,
    mut v___y_7587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7589_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___redArg(v_name_7575_, v_type_7576_, v_val_7577_, v_k_7578_, v_nondep_7579_, v_kind_7580_, v___y_7581_, v___y_7582_, v___y_7583_, v___y_7584_, v___y_7585_, v___y_7586_, v___y_7587_);
    return v___x_7589_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23___boxed(
    mut v_00_u03b1_7590_: *mut crate::leanh::LeanObject,
    mut v_name_7591_: *mut crate::leanh::LeanObject,
    mut v_type_7592_: *mut crate::leanh::LeanObject,
    mut v_val_7593_: *mut crate::leanh::LeanObject,
    mut v_k_7594_: *mut crate::leanh::LeanObject,
    mut v_nondep_7595_: *mut crate::leanh::LeanObject,
    mut v_kind_7596_: *mut crate::leanh::LeanObject,
    mut v___y_7597_: *mut crate::leanh::LeanObject,
    mut v___y_7598_: *mut crate::leanh::LeanObject,
    mut v___y_7599_: *mut crate::leanh::LeanObject,
    mut v___y_7600_: *mut crate::leanh::LeanObject,
    mut v___y_7601_: *mut crate::leanh::LeanObject,
    mut v___y_7602_: *mut crate::leanh::LeanObject,
    mut v___y_7603_: *mut crate::leanh::LeanObject,
    mut v___y_7604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_7605_: u8 = 0;
    let mut v_kind_boxed_7606_: u8 = 0;
    let mut v___y_67235__boxed_7607_: u8 = 0;
    let mut v_res_7608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_7605_ = (crate::leanh::lean_unbox(v_nondep_7595_) as u8);
    v_kind_boxed_7606_ = (crate::leanh::lean_unbox(v_kind_7596_) as u8);
    v___y_67235__boxed_7607_ = (crate::leanh::lean_unbox(v___y_7597_) as u8);
    v_res_7608_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLet_spec__23(v_00_u03b1_7590_, v_name_7591_, v_type_7592_, v_val_7593_, v_k_7594_, v_nondep_boxed_7605_, v_kind_boxed_7606_, v___y_67235__boxed_7607_, v___y_7598_, v___y_7599_, v___y_7600_, v___y_7601_, v___y_7602_, v___y_7603_);
    crate::leanh::lean_dec(v___y_7603_);
    crate::leanh::lean_dec_ref(v___y_7602_);
    crate::leanh::lean_dec(v___y_7601_);
    crate::leanh::lean_dec_ref(v___y_7600_);
    crate::leanh::lean_dec(v___y_7599_);
    crate::leanh::lean_dec_ref(v___y_7598_);
    return v_res_7608_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(
    mut v_00_u03b1_7609_: *mut crate::leanh::LeanObject,
    mut v_name_7610_: *mut crate::leanh::LeanObject,
    mut v_bi_7611_: u8,
    mut v_type_7612_: *mut crate::leanh::LeanObject,
    mut v_k_7613_: *mut crate::leanh::LeanObject,
    mut v_kind_7614_: u8,
    mut v___y_7615_: u8,
    mut v___y_7616_: *mut crate::leanh::LeanObject,
    mut v___y_7617_: *mut crate::leanh::LeanObject,
    mut v___y_7618_: *mut crate::leanh::LeanObject,
    mut v___y_7619_: *mut crate::leanh::LeanObject,
    mut v___y_7620_: *mut crate::leanh::LeanObject,
    mut v___y_7621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7623_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___redArg(v_name_7610_, v_bi_7611_, v_type_7612_, v_k_7613_, v_kind_7614_, v___y_7615_, v___y_7616_, v___y_7617_, v___y_7618_, v___y_7619_, v___y_7620_, v___y_7621_);
    return v___x_7623_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26___boxed(
    mut v_00_u03b1_7624_: *mut crate::leanh::LeanObject,
    mut v_name_7625_: *mut crate::leanh::LeanObject,
    mut v_bi_7626_: *mut crate::leanh::LeanObject,
    mut v_type_7627_: *mut crate::leanh::LeanObject,
    mut v_k_7628_: *mut crate::leanh::LeanObject,
    mut v_kind_7629_: *mut crate::leanh::LeanObject,
    mut v___y_7630_: *mut crate::leanh::LeanObject,
    mut v___y_7631_: *mut crate::leanh::LeanObject,
    mut v___y_7632_: *mut crate::leanh::LeanObject,
    mut v___y_7633_: *mut crate::leanh::LeanObject,
    mut v___y_7634_: *mut crate::leanh::LeanObject,
    mut v___y_7635_: *mut crate::leanh::LeanObject,
    mut v___y_7636_: *mut crate::leanh::LeanObject,
    mut v___y_7637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_7638_: u8 = 0;
    let mut v_kind_boxed_7639_: u8 = 0;
    let mut v___y_67261__boxed_7640_: u8 = 0;
    let mut v_res_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_7638_ = (crate::leanh::lean_unbox(v_bi_7626_) as u8);
    v_kind_boxed_7639_ = (crate::leanh::lean_unbox(v_kind_7629_) as u8);
    v___y_67261__boxed_7640_ = (crate::leanh::lean_unbox(v___y_7630_) as u8);
    v_res_7641_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonLambdaLoop_spec__26(v_00_u03b1_7624_, v_name_7625_, v_bi_boxed_7638_, v_type_7627_, v_k_7628_, v_kind_boxed_7639_, v___y_67261__boxed_7640_, v___y_7631_, v___y_7632_, v___y_7633_, v___y_7634_, v___y_7635_, v___y_7636_);
    crate::leanh::lean_dec(v___y_7636_);
    crate::leanh::lean_dec_ref(v___y_7635_);
    crate::leanh::lean_dec(v___y_7634_);
    crate::leanh::lean_dec_ref(v___y_7633_);
    crate::leanh::lean_dec(v___y_7632_);
    crate::leanh::lean_dec_ref(v___y_7631_);
    return v_res_7641_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(
    mut v_00_u03b2_7642_: *mut crate::leanh::LeanObject,
    mut v_m_7643_: *mut crate::leanh::LeanObject,
    mut v_a_7644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___redArg(v_m_7643_, v_a_7644_);
    return v___x_7645_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1___boxed(
    mut v_00_u03b2_7646_: *mut crate::leanh::LeanObject,
    mut v_m_7647_: *mut crate::leanh::LeanObject,
    mut v_a_7648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1(v_00_u03b2_7646_, v_m_7647_, v_a_7648_);
    crate::leanh::lean_dec_ref(v_a_7648_);
    crate::leanh::lean_dec_ref(v_m_7647_);
    return v_res_7649_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2(
    mut v_00_u03b2_7650_: *mut crate::leanh::LeanObject,
    mut v_m_7651_: *mut crate::leanh::LeanObject,
    mut v_a_7652_: *mut crate::leanh::LeanObject,
    mut v_b_7653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7654_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2___redArg(v_m_7651_, v_a_7652_, v_b_7653_);
    return v___x_7654_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(
    mut v_cls_7655_: *mut crate::leanh::LeanObject,
    mut v_msg_7656_: *mut crate::leanh::LeanObject,
    mut v___y_7657_: u8,
    mut v___y_7658_: *mut crate::leanh::LeanObject,
    mut v___y_7659_: *mut crate::leanh::LeanObject,
    mut v___y_7660_: *mut crate::leanh::LeanObject,
    mut v___y_7661_: *mut crate::leanh::LeanObject,
    mut v___y_7662_: *mut crate::leanh::LeanObject,
    mut v___y_7663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7665_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___redArg(v_cls_7655_, v_msg_7656_, v___y_7660_, v___y_7661_, v___y_7662_, v___y_7663_);
    return v___x_7665_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9___boxed(
    mut v_cls_7666_: *mut crate::leanh::LeanObject,
    mut v_msg_7667_: *mut crate::leanh::LeanObject,
    mut v___y_7668_: *mut crate::leanh::LeanObject,
    mut v___y_7669_: *mut crate::leanh::LeanObject,
    mut v___y_7670_: *mut crate::leanh::LeanObject,
    mut v___y_7671_: *mut crate::leanh::LeanObject,
    mut v___y_7672_: *mut crate::leanh::LeanObject,
    mut v___y_7673_: *mut crate::leanh::LeanObject,
    mut v___y_7674_: *mut crate::leanh::LeanObject,
    mut v___y_7675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_67291__boxed_7676_: u8 = 0;
    let mut v_res_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_67291__boxed_7676_ = (crate::leanh::lean_unbox(v___y_7668_) as u8);
    v_res_7677_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__9(v_cls_7666_, v_msg_7667_, v___y_67291__boxed_7676_, v___y_7669_, v___y_7670_, v___y_7671_, v___y_7672_, v___y_7673_, v___y_7674_);
    crate::leanh::lean_dec(v___y_7674_);
    crate::leanh::lean_dec_ref(v___y_7673_);
    crate::leanh::lean_dec(v___y_7672_);
    crate::leanh::lean_dec_ref(v___y_7671_);
    crate::leanh::lean_dec(v___y_7670_);
    crate::leanh::lean_dec_ref(v___y_7669_);
    return v_res_7677_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(
    mut v_upperBound_7678_: *mut crate::leanh::LeanObject,
    mut v___x_7679_: *mut crate::leanh::LeanObject,
    mut v___x_7680_: *mut crate::leanh::LeanObject,
    mut v_inst_7681_: *mut crate::leanh::LeanObject,
    mut v_R_7682_: *mut crate::leanh::LeanObject,
    mut v_a_7683_: *mut crate::leanh::LeanObject,
    mut v_b_7684_: *mut crate::leanh::LeanObject,
    mut v_c_7685_: *mut crate::leanh::LeanObject,
    mut v___y_7686_: u8,
    mut v___y_7687_: *mut crate::leanh::LeanObject,
    mut v___y_7688_: *mut crate::leanh::LeanObject,
    mut v___y_7689_: *mut crate::leanh::LeanObject,
    mut v___y_7690_: *mut crate::leanh::LeanObject,
    mut v___y_7691_: *mut crate::leanh::LeanObject,
    mut v___y_7692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___redArg(v_upperBound_7678_, v___x_7680_, v_a_7683_, v_b_7684_, v___y_7686_, v___y_7687_, v___y_7688_, v___y_7689_, v___y_7690_, v___y_7691_, v___y_7692_);
    return v___x_7694_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10___boxed(
    mut v_upperBound_7695_: *mut crate::leanh::LeanObject,
    mut v___x_7696_: *mut crate::leanh::LeanObject,
    mut v___x_7697_: *mut crate::leanh::LeanObject,
    mut v_inst_7698_: *mut crate::leanh::LeanObject,
    mut v_R_7699_: *mut crate::leanh::LeanObject,
    mut v_a_7700_: *mut crate::leanh::LeanObject,
    mut v_b_7701_: *mut crate::leanh::LeanObject,
    mut v_c_7702_: *mut crate::leanh::LeanObject,
    mut v___y_7703_: *mut crate::leanh::LeanObject,
    mut v___y_7704_: *mut crate::leanh::LeanObject,
    mut v___y_7705_: *mut crate::leanh::LeanObject,
    mut v___y_7706_: *mut crate::leanh::LeanObject,
    mut v___y_7707_: *mut crate::leanh::LeanObject,
    mut v___y_7708_: *mut crate::leanh::LeanObject,
    mut v___y_7709_: *mut crate::leanh::LeanObject,
    mut v___y_7710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_67321__boxed_7711_: u8 = 0;
    let mut v_res_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_67321__boxed_7711_ = (crate::leanh::lean_unbox(v___y_7703_) as u8);
    v_res_7712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_canonAppDefault_spec__10(v_upperBound_7695_, v___x_7696_, v___x_7697_, v_inst_7698_, v_R_7699_, v_a_7700_, v_b_7701_, v_c_7702_, v___y_67321__boxed_7711_, v___y_7704_, v___y_7705_, v___y_7706_, v___y_7707_, v___y_7708_, v___y_7709_);
    crate::leanh::lean_dec(v___y_7709_);
    crate::leanh::lean_dec_ref(v___y_7708_);
    crate::leanh::lean_dec(v___y_7707_);
    crate::leanh::lean_dec_ref(v___y_7706_);
    crate::leanh::lean_dec(v___y_7705_);
    crate::leanh::lean_dec_ref(v___y_7704_);
    crate::leanh::lean_dec_ref(v___x_7697_);
    crate::leanh::lean_dec(v___x_7696_);
    crate::leanh::lean_dec(v_upperBound_7695_);
    return v_res_7712_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(
    mut v_00_u03b2_7713_: *mut crate::leanh::LeanObject,
    mut v_a_7714_: *mut crate::leanh::LeanObject,
    mut v_x_7715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7716_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___redArg(v_a_7714_, v_x_7715_);
    return v___x_7716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10___boxed(
    mut v_00_u03b2_7717_: *mut crate::leanh::LeanObject,
    mut v_a_7718_: *mut crate::leanh::LeanObject,
    mut v_x_7719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7720_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__1_spec__10(v_00_u03b2_7717_, v_a_7718_, v_x_7719_);
    crate::leanh::lean_dec(v_x_7719_);
    crate::leanh::lean_dec_ref(v_a_7718_);
    return v_res_7720_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(
    mut v_00_u03b2_7721_: *mut crate::leanh::LeanObject,
    mut v_a_7722_: *mut crate::leanh::LeanObject,
    mut v_x_7723_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7724_: u8 = 0;
    v___x_7724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___redArg(v_a_7722_, v_x_7723_);
    return v___x_7724_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12___boxed(
    mut v_00_u03b2_7725_: *mut crate::leanh::LeanObject,
    mut v_a_7726_: *mut crate::leanh::LeanObject,
    mut v_x_7727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7728_: u8 = 0;
    let mut v_r_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__12(v_00_u03b2_7725_, v_a_7726_, v_x_7727_);
    crate::leanh::lean_dec(v_x_7727_);
    crate::leanh::lean_dec_ref(v_a_7726_);
    v_r_7729_ = crate::leanh::lean_box((v_res_7728_) as usize);
    return v_r_7729_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13(
    mut v_00_u03b2_7730_: *mut crate::leanh::LeanObject,
    mut v_data_7731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7732_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13___redArg(v_data_7731_);
    return v___x_7732_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14(
    mut v_00_u03b2_7733_: *mut crate::leanh::LeanObject,
    mut v_a_7734_: *mut crate::leanh::LeanObject,
    mut v_b_7735_: *mut crate::leanh::LeanObject,
    mut v_x_7736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7737_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__14___redArg(v_a_7734_, v_b_7735_, v_x_7736_);
    return v___x_7737_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27(
    mut v_00_u03b2_7738_: *mut crate::leanh::LeanObject,
    mut v_i_7739_: *mut crate::leanh::LeanObject,
    mut v_source_7740_: *mut crate::leanh::LeanObject,
    mut v_target_7741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7742_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27___redArg(v_i_7739_, v_source_7740_, v_target_7741_);
    return v___x_7742_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32(
    mut v_00_u03b2_7743_: *mut crate::leanh::LeanObject,
    mut v_x_7744_: *mut crate::leanh::LeanObject,
    mut v_x_7745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon_spec__2_spec__13_spec__27_spec__32___redArg(v_x_7744_, v_x_7745_);
    return v___x_7746_;
}
pub unsafe fn l_Lean_Meta_Sym_Canon_isSupport(
    mut v_pinfos_7747_: *mut crate::leanh::LeanObject,
    mut v_i_7748_: *mut crate::leanh::LeanObject,
    mut v_arg_7749_: *mut crate::leanh::LeanObject,
    mut v_a_7750_: *mut crate::leanh::LeanObject,
    mut v_a_7751_: *mut crate::leanh::LeanObject,
    mut v_a_7752_: *mut crate::leanh::LeanObject,
    mut v_a_7753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7759_: u8 = 0;
    let mut v___x_7760_: u8 = 0;
    let mut v___x_7761_: u8 = 0;
    let mut v___x_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: u8 = 0;
    let mut v___x_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7771_: u8 = 0;
    let mut v_a_7772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7775_: u8 = 0;
    let mut v___x_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7755_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_shouldCanon(
                    v_pinfos_7747_,
                    v_i_7748_,
                    v_arg_7749_,
                    v_a_7750_,
                    v_a_7751_,
                    v_a_7752_,
                    v_a_7753_,
                );
                if crate::leanh::lean_obj_tag(v___x_7755_) == 0 {
                    v_a_7756_ = crate::leanh::lean_ctor_get(v___x_7755_, 0);
                    v_isSharedCheck_7771_ = (!crate::leanh::lean_is_exclusive(v___x_7755_)) as u8;
                    if v_isSharedCheck_7771_ == 0 {
                        v___x_7758_ = v___x_7755_;
                        v_isShared_7759_ = v_isSharedCheck_7771_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7756_);
                        crate::leanh::lean_dec(v___x_7755_);
                        v___x_7758_ = crate::leanh::lean_box(0);
                        v_isShared_7759_ = v_isSharedCheck_7771_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7772_ = crate::leanh::lean_ctor_get(v___x_7755_, 0);
                    v_isSharedCheck_7779_ = (!crate::leanh::lean_is_exclusive(v___x_7755_)) as u8;
                    if v_isSharedCheck_7779_ == 0 {
                        v___x_7774_ = v___x_7755_;
                        v_isShared_7775_ = v_isSharedCheck_7779_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7772_);
                        crate::leanh::lean_dec(v___x_7755_);
                        v___x_7774_ = crate::leanh::lean_box(0);
                        v_isShared_7775_ = v_isSharedCheck_7779_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7760_ = (crate::leanh::lean_unbox(v_a_7756_) as u8);
                crate::leanh::lean_dec(v_a_7756_);
                if v___x_7760_ == 3 {
                    v___x_7761_ = 0;
                    v___x_7762_ = crate::leanh::lean_box((v___x_7761_) as usize);
                    if v_isShared_7759_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7758_, 0, v___x_7762_);
                        v___x_7764_ = v___x_7758_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7765_, 0, v___x_7762_);
                        v___x_7764_ = v_reuseFailAlloc_7765_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7766_ = 1;
                    v___x_7767_ = crate::leanh::lean_box((v___x_7766_) as usize);
                    if v_isShared_7759_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7758_, 0, v___x_7767_);
                        v___x_7769_ = v___x_7758_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7770_, 0, v___x_7767_);
                        v___x_7769_ = v_reuseFailAlloc_7770_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7764_;
            }
            3 => {
                return v___x_7769_;
            }
            4 => {
                if v_isShared_7775_ == 0 {
                    v___x_7777_ = v___x_7774_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7778_, 0, v_a_7772_);
                    v___x_7777_ = v_reuseFailAlloc_7778_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Canon_isSupport___boxed(
    mut v_pinfos_7780_: *mut crate::leanh::LeanObject,
    mut v_i_7781_: *mut crate::leanh::LeanObject,
    mut v_arg_7782_: *mut crate::leanh::LeanObject,
    mut v_a_7783_: *mut crate::leanh::LeanObject,
    mut v_a_7784_: *mut crate::leanh::LeanObject,
    mut v_a_7785_: *mut crate::leanh::LeanObject,
    mut v_a_7786_: *mut crate::leanh::LeanObject,
    mut v_a_7787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7788_ = l_Lean_Meta_Sym_Canon_isSupport(
        v_pinfos_7780_,
        v_i_7781_,
        v_arg_7782_,
        v_a_7783_,
        v_a_7784_,
        v_a_7785_,
        v_a_7786_,
    );
    crate::leanh::lean_dec(v_a_7786_);
    crate::leanh::lean_dec_ref(v_a_7785_);
    crate::leanh::lean_dec(v_a_7784_);
    crate::leanh::lean_dec_ref(v_a_7783_);
    crate::leanh::lean_dec(v_i_7781_);
    crate::leanh::lean_dec_ref(v_pinfos_7780_);
    return v_res_7788_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(
    mut v_category_7789_: *mut crate::leanh::LeanObject,
    mut v_opts_7790_: *mut crate::leanh::LeanObject,
    mut v_act_7791_: *mut crate::leanh::LeanObject,
    mut v_decl_7792_: *mut crate::leanh::LeanObject,
    mut v___y_7793_: *mut crate::leanh::LeanObject,
    mut v___y_7794_: *mut crate::leanh::LeanObject,
    mut v___y_7795_: *mut crate::leanh::LeanObject,
    mut v___y_7796_: *mut crate::leanh::LeanObject,
    mut v___y_7797_: *mut crate::leanh::LeanObject,
    mut v___y_7798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_7798_);
    crate::leanh::lean_inc_ref(v___y_7797_);
    crate::leanh::lean_inc(v___y_7796_);
    crate::leanh::lean_inc_ref(v___y_7795_);
    crate::leanh::lean_inc(v___y_7794_);
    crate::leanh::lean_inc_ref(v___y_7793_);
    v___x_7800_ = crate::leanh::lean_apply_6(
        v_act_7791_,
        v___y_7793_,
        v___y_7794_,
        v___y_7795_,
        v___y_7796_,
        v___y_7797_,
        v___y_7798_,
    );
    v___x_7801_ = l_Lean_profileitIOUnsafe___redArg(
        v_category_7789_,
        v_opts_7790_,
        v___x_7800_,
        v_decl_7792_,
    );
    return v___x_7801_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg___boxed(
    mut v_category_7802_: *mut crate::leanh::LeanObject,
    mut v_opts_7803_: *mut crate::leanh::LeanObject,
    mut v_act_7804_: *mut crate::leanh::LeanObject,
    mut v_decl_7805_: *mut crate::leanh::LeanObject,
    mut v___y_7806_: *mut crate::leanh::LeanObject,
    mut v___y_7807_: *mut crate::leanh::LeanObject,
    mut v___y_7808_: *mut crate::leanh::LeanObject,
    mut v___y_7809_: *mut crate::leanh::LeanObject,
    mut v___y_7810_: *mut crate::leanh::LeanObject,
    mut v___y_7811_: *mut crate::leanh::LeanObject,
    mut v___y_7812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7813_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(
        v_category_7802_,
        v_opts_7803_,
        v_act_7804_,
        v_decl_7805_,
        v___y_7806_,
        v___y_7807_,
        v___y_7808_,
        v___y_7809_,
        v___y_7810_,
        v___y_7811_,
    );
    crate::leanh::lean_dec(v___y_7811_);
    crate::leanh::lean_dec_ref(v___y_7810_);
    crate::leanh::lean_dec(v___y_7809_);
    crate::leanh::lean_dec_ref(v___y_7808_);
    crate::leanh::lean_dec(v___y_7807_);
    crate::leanh::lean_dec_ref(v___y_7806_);
    crate::leanh::lean_dec_ref(v_opts_7803_);
    crate::leanh::lean_dec_ref(v_category_7802_);
    return v_res_7813_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(
    mut v_00_u03b1_7814_: *mut crate::leanh::LeanObject,
    mut v_category_7815_: *mut crate::leanh::LeanObject,
    mut v_opts_7816_: *mut crate::leanh::LeanObject,
    mut v_act_7817_: *mut crate::leanh::LeanObject,
    mut v_decl_7818_: *mut crate::leanh::LeanObject,
    mut v___y_7819_: *mut crate::leanh::LeanObject,
    mut v___y_7820_: *mut crate::leanh::LeanObject,
    mut v___y_7821_: *mut crate::leanh::LeanObject,
    mut v___y_7822_: *mut crate::leanh::LeanObject,
    mut v___y_7823_: *mut crate::leanh::LeanObject,
    mut v___y_7824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7826_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(
        v_category_7815_,
        v_opts_7816_,
        v_act_7817_,
        v_decl_7818_,
        v___y_7819_,
        v___y_7820_,
        v___y_7821_,
        v___y_7822_,
        v___y_7823_,
        v___y_7824_,
    );
    return v___x_7826_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___boxed(
    mut v_00_u03b1_7827_: *mut crate::leanh::LeanObject,
    mut v_category_7828_: *mut crate::leanh::LeanObject,
    mut v_opts_7829_: *mut crate::leanh::LeanObject,
    mut v_act_7830_: *mut crate::leanh::LeanObject,
    mut v_decl_7831_: *mut crate::leanh::LeanObject,
    mut v___y_7832_: *mut crate::leanh::LeanObject,
    mut v___y_7833_: *mut crate::leanh::LeanObject,
    mut v___y_7834_: *mut crate::leanh::LeanObject,
    mut v___y_7835_: *mut crate::leanh::LeanObject,
    mut v___y_7836_: *mut crate::leanh::LeanObject,
    mut v___y_7837_: *mut crate::leanh::LeanObject,
    mut v___y_7838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7839_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0(
        v_00_u03b1_7827_,
        v_category_7828_,
        v_opts_7829_,
        v_act_7830_,
        v_decl_7831_,
        v___y_7832_,
        v___y_7833_,
        v___y_7834_,
        v___y_7835_,
        v___y_7836_,
        v___y_7837_,
    );
    crate::leanh::lean_dec(v___y_7837_);
    crate::leanh::lean_dec_ref(v___y_7836_);
    crate::leanh::lean_dec(v___y_7835_);
    crate::leanh::lean_dec_ref(v___y_7834_);
    crate::leanh::lean_dec(v___y_7833_);
    crate::leanh::lean_dec_ref(v___y_7832_);
    crate::leanh::lean_dec_ref(v_opts_7829_);
    crate::leanh::lean_dec_ref(v_category_7828_);
    return v_res_7839_;
}
pub unsafe fn l_Lean_Meta_Sym_canon___lam__0(
    mut v___x_7840_: u8,
    mut v_e_7841_: *mut crate::leanh::LeanObject,
    mut v___x_7842_: u8,
    mut v___y_7843_: *mut crate::leanh::LeanObject,
    mut v___y_7844_: *mut crate::leanh::LeanObject,
    mut v___y_7845_: *mut crate::leanh::LeanObject,
    mut v___y_7846_: *mut crate::leanh::LeanObject,
    mut v___y_7847_: *mut crate::leanh::LeanObject,
    mut v___y_7848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_7851_: u8 = 0;
    let mut v_ctxApprox_7852_: u8 = 0;
    let mut v_quasiPatternApprox_7853_: u8 = 0;
    let mut v_constApprox_7854_: u8 = 0;
    let mut v_isDefEqStuckEx_7855_: u8 = 0;
    let mut v_unificationHints_7856_: u8 = 0;
    let mut v_proofIrrelevance_7857_: u8 = 0;
    let mut v_assignSyntheticOpaque_7858_: u8 = 0;
    let mut v_offsetCnstrs_7859_: u8 = 0;
    let mut v_etaStruct_7860_: u8 = 0;
    let mut v_univApprox_7861_: u8 = 0;
    let mut v_iota_7862_: u8 = 0;
    let mut v_beta_7863_: u8 = 0;
    let mut v_proj_7864_: u8 = 0;
    let mut v_zeta_7865_: u8 = 0;
    let mut v_zetaDelta_7866_: u8 = 0;
    let mut v_zetaUnused_7867_: u8 = 0;
    let mut v_zetaHave_7868_: u8 = 0;
    let mut v___x_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7871_: u8 = 0;
    let mut v_trackZetaDelta_7872_: u8 = 0;
    let mut v_zetaDeltaSet_7873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7879_: u8 = 0;
    let mut v_inTypeClassResolution_7880_: u8 = 0;
    let mut v_cacheInferType_7881_: u8 = 0;
    let mut v_config_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: u64 = 0;
    let mut v___x_7885_: u64 = 0;
    let mut v___x_7886_: u64 = 0;
    let mut v___x_7887_: u64 = 0;
    let mut v___x_7888_: u64 = 0;
    let mut v_key_7889_: u64 = 0;
    let mut v___x_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7850_ = l_Lean_Meta_Context_config(v___y_7845_);
                v_foApprox_7851_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 0 as u32);
                v_ctxApprox_7852_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 1 as u32);
                v_quasiPatternApprox_7853_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_7850_, 2 as u32);
                v_constApprox_7854_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 3 as u32);
                v_isDefEqStuckEx_7855_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 4 as u32);
                v_unificationHints_7856_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 5 as u32);
                v_proofIrrelevance_7857_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 6 as u32);
                v_assignSyntheticOpaque_7858_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_7850_, 7 as u32);
                v_offsetCnstrs_7859_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 8 as u32);
                v_etaStruct_7860_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 10 as u32);
                v_univApprox_7861_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 11 as u32);
                v_iota_7862_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 12 as u32);
                v_beta_7863_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 13 as u32);
                v_proj_7864_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 14 as u32);
                v_zeta_7865_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 15 as u32);
                v_zetaDelta_7866_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 16 as u32);
                v_zetaUnused_7867_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 17 as u32);
                v_zetaHave_7868_ = crate::leanh::lean_ctor_get_uint8(v___x_7850_, 18 as u32);
                v_isSharedCheck_7894_ = (!crate::leanh::lean_is_exclusive(v___x_7850_)) as u8;
                if v_isSharedCheck_7894_ == 0 {
                    v___x_7870_ = v___x_7850_;
                    v_isShared_7871_ = v_isSharedCheck_7894_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_7850_);
                    v___x_7870_ = crate::leanh::lean_box(0);
                    v_isShared_7871_ = v_isSharedCheck_7894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_7872_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7845_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_7873_ = crate::leanh::lean_ctor_get(v___y_7845_, 1);
                v_lctx_7874_ = crate::leanh::lean_ctor_get(v___y_7845_, 2);
                v_localInstances_7875_ = crate::leanh::lean_ctor_get(v___y_7845_, 3);
                v_defEqCtx_x3f_7876_ = crate::leanh::lean_ctor_get(v___y_7845_, 4);
                v_synthPendingDepth_7877_ = crate::leanh::lean_ctor_get(v___y_7845_, 5);
                v_canUnfold_x3f_7878_ = crate::leanh::lean_ctor_get(v___y_7845_, 6);
                v_univApprox_7879_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7845_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7880_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7845_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7881_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7845_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_7871_ == 0 {
                    v_config_7883_ = v___x_7870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7893_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        0 as u32,
                        v_foApprox_7851_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        1 as u32,
                        v_ctxApprox_7852_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        2 as u32,
                        v_quasiPatternApprox_7853_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        3 as u32,
                        v_constApprox_7854_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        4 as u32,
                        v_isDefEqStuckEx_7855_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        5 as u32,
                        v_unificationHints_7856_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        6 as u32,
                        v_proofIrrelevance_7857_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        7 as u32,
                        v_assignSyntheticOpaque_7858_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        8 as u32,
                        v_offsetCnstrs_7859_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        10 as u32,
                        v_etaStruct_7860_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        11 as u32,
                        v_univApprox_7861_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        12 as u32,
                        v_iota_7862_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        13 as u32,
                        v_beta_7863_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        14 as u32,
                        v_proj_7864_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        15 as u32,
                        v_zeta_7865_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        16 as u32,
                        v_zetaDelta_7866_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        17 as u32,
                        v_zetaUnused_7867_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7893_,
                        18 as u32,
                        v_zetaHave_7868_,
                    );
                    v_config_7883_ = v_reuseFailAlloc_7893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_7883_, 9 as u32, v___x_7840_);
                v___x_7884_ = l_Lean_Meta_Context_configKey(v___y_7845_);
                v___x_7885_ = 3u64;
                v___x_7886_ = lean_uint64_shift_right(v___x_7884_, v___x_7885_);
                v___x_7887_ = lean_uint64_shift_left(v___x_7886_, v___x_7885_);
                v___x_7888_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_7840_);
                v_key_7889_ = lean_uint64_lor(v___x_7887_, v___x_7888_);
                v___x_7890_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_7890_, 0, v_config_7883_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_7890_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_7889_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_7878_);
                crate::leanh::lean_inc(v_synthPendingDepth_7877_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_7876_);
                crate::leanh::lean_inc_ref(v_localInstances_7875_);
                crate::leanh::lean_inc_ref(v_lctx_7874_);
                crate::leanh::lean_inc(v_zetaDeltaSet_7873_);
                v___x_7891_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_7891_, 0, v___x_7890_);
                crate::leanh::lean_ctor_set(v___x_7891_, 1, v_zetaDeltaSet_7873_);
                crate::leanh::lean_ctor_set(v___x_7891_, 2, v_lctx_7874_);
                crate::leanh::lean_ctor_set(v___x_7891_, 3, v_localInstances_7875_);
                crate::leanh::lean_ctor_set(v___x_7891_, 4, v_defEqCtx_x3f_7876_);
                crate::leanh::lean_ctor_set(v___x_7891_, 5, v_synthPendingDepth_7877_);
                crate::leanh::lean_ctor_set(v___x_7891_, 6, v_canUnfold_x3f_7878_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7891_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_7872_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7891_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7879_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7891_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7880_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7891_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7881_,
                );
                v___x_7892_ = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_canon(
                    v_e_7841_,
                    v___x_7842_,
                    v___y_7843_,
                    v___y_7844_,
                    v___x_7891_,
                    v___y_7846_,
                    v___y_7847_,
                    v___y_7848_,
                );
                crate::leanh::lean_dec_ref_known(v___x_7891_, 7);
                return v___x_7892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_canon___lam__0___boxed(
    mut v___x_7895_: *mut crate::leanh::LeanObject,
    mut v_e_7896_: *mut crate::leanh::LeanObject,
    mut v___x_7897_: *mut crate::leanh::LeanObject,
    mut v___y_7898_: *mut crate::leanh::LeanObject,
    mut v___y_7899_: *mut crate::leanh::LeanObject,
    mut v___y_7900_: *mut crate::leanh::LeanObject,
    mut v___y_7901_: *mut crate::leanh::LeanObject,
    mut v___y_7902_: *mut crate::leanh::LeanObject,
    mut v___y_7903_: *mut crate::leanh::LeanObject,
    mut v___y_7904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2440__boxed_7905_: u8 = 0;
    let mut v___x_2441__boxed_7906_: u8 = 0;
    let mut v_res_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2440__boxed_7905_ = (crate::leanh::lean_unbox(v___x_7895_) as u8);
    v___x_2441__boxed_7906_ = (crate::leanh::lean_unbox(v___x_7897_) as u8);
    v_res_7907_ = l_Lean_Meta_Sym_canon___lam__0(
        v___x_2440__boxed_7905_,
        v_e_7896_,
        v___x_2441__boxed_7906_,
        v___y_7898_,
        v___y_7899_,
        v___y_7900_,
        v___y_7901_,
        v___y_7902_,
        v___y_7903_,
    );
    crate::leanh::lean_dec(v___y_7903_);
    crate::leanh::lean_dec_ref(v___y_7902_);
    crate::leanh::lean_dec(v___y_7901_);
    crate::leanh::lean_dec_ref(v___y_7900_);
    crate::leanh::lean_dec(v___y_7899_);
    crate::leanh::lean_dec_ref(v___y_7898_);
    return v_res_7907_;
}
pub unsafe fn l_Lean_Meta_Sym_canon(
    mut v_e_7909_: *mut crate::leanh::LeanObject,
    mut v_a_7910_: *mut crate::leanh::LeanObject,
    mut v_a_7911_: *mut crate::leanh::LeanObject,
    mut v_a_7912_: *mut crate::leanh::LeanObject,
    mut v_a_7913_: *mut crate::leanh::LeanObject,
    mut v_a_7914_: *mut crate::leanh::LeanObject,
    mut v_a_7915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: u8 = 0;
    let mut v___x_7920_: u8 = 0;
    let mut v___x_7921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_7917_ = crate::leanh::lean_ctor_get(v_a_7914_, 2);
    v___x_7918_ = l_Lean_Meta_Sym_canon___closed__0;
    v___x_7919_ = 0;
    v___x_7920_ = 2;
    v___x_7921_ = crate::leanh::lean_box((v___x_7920_) as usize);
    v___x_7922_ = crate::leanh::lean_box((v___x_7919_) as usize);
    v___f_7923_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_canon___lam__0___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7923_, 0, v___x_7921_);
    crate::leanh::lean_closure_set(v___f_7923_, 1, v_e_7909_);
    crate::leanh::lean_closure_set(v___f_7923_, 2, v___x_7922_);
    v___x_7924_ = crate::leanh::lean_box(0);
    v___x_7925_ = l_Lean_profileitM___at___00Lean_Meta_Sym_canon_spec__0___redArg(
        v___x_7918_,
        v_options_7917_,
        v___f_7923_,
        v___x_7924_,
        v_a_7910_,
        v_a_7911_,
        v_a_7912_,
        v_a_7913_,
        v_a_7914_,
        v_a_7915_,
    );
    return v___x_7925_;
}
pub unsafe fn l_Lean_Meta_Sym_canon___boxed(
    mut v_e_7926_: *mut crate::leanh::LeanObject,
    mut v_a_7927_: *mut crate::leanh::LeanObject,
    mut v_a_7928_: *mut crate::leanh::LeanObject,
    mut v_a_7929_: *mut crate::leanh::LeanObject,
    mut v_a_7930_: *mut crate::leanh::LeanObject,
    mut v_a_7931_: *mut crate::leanh::LeanObject,
    mut v_a_7932_: *mut crate::leanh::LeanObject,
    mut v_a_7933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7934_ = l_Lean_Meta_Sym_canon(
        v_e_7926_, v_a_7927_, v_a_7928_, v_a_7929_, v_a_7930_, v_a_7931_, v_a_7932_,
    );
    crate::leanh::lean_dec(v_a_7932_);
    crate::leanh::lean_dec_ref(v_a_7931_);
    crate::leanh::lean_dec(v_a_7930_);
    crate::leanh::lean_dec_ref(v_a_7929_);
    crate::leanh::lean_dec(v_a_7928_);
    crate::leanh::lean_dec_ref(v_a_7927_);
    return v_res_7934_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Canon(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_initFn_00___x40_Lean_Meta_Sym_Canon_1925315962____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default =
        _init_l_Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult_default();
    l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult =
        _init_l___private_Lean_Meta_Sym_Canon_0__Lean_Meta_Sym_Canon_instInhabitedShouldCanonResult(
        );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Canon(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Canon(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Canon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Canon(builtin);
}
