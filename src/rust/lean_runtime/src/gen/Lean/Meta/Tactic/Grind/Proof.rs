// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Proof
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Lemmas Init.Grind.Util
use crate::r#gen::Init::Grind::Lemmas::{
    initialize_Init_Grind_Lemmas, runtime_initialize_Init_Grind_Lemmas,
};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isConstOf, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkApp7,
    l_Lean_mkApp8, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkCongr, l_Lean_Meta_mkCongrArg, l_Lean_Meta_mkCongrFun, l_Lean_Meta_mkEqNDRec,
    l_Lean_Meta_mkEqOfHEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkEqSymm, l_Lean_Meta_mkEqTrans,
    l_Lean_Meta_mkHEq, l_Lean_Meta_mkHEqOfEq, l_Lean_Meta_mkHEqRefl, l_Lean_Meta_mkHEqSymm,
    l_Lean_Meta_mkHEqTrans,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::FunInfo::{l_Lean_Meta_FunInfo_getArity, l_Lean_Meta_getFunInfo};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_Goal_getENode,
    l_Lean_Meta_Grind_Goal_hasSameRoot, l_Lean_Meta_Grind_congrPlaceholderProof,
    l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof, l_Lean_Meta_Grind_getRootENode___redArg,
    l_Lean_Meta_Grind_hasSameType, l_Lean_Meta_Grind_instInhabitedGoalM,
    l_Lean_Meta_Grind_mkHCongrWithArity___redArg, l_Lean_Meta_Grind_useFunCC___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_11,
    lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1_value
) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 102, 105, 110, 100, 67, 111, 109, 109, 111, 110, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0_value: LeanStringObject<80> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [96, 103, 114, 105, 110, 100, 96, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 99, 97, 110, 110, 111, 116, 32, 98, 117, 105, 108, 100, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 112, 114, 111, 111, 102, 115, 32, 102, 111, 114, 32, 111, 118, 101, 114, 45, 97, 112, 112, 108, 105, 101, 100, 32, 116, 101, 114, 109, 115, 32, 115, 117, 99, 104, 32, 97, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [10, 97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 116, 104, 109, 46, 97, 114, 103, 75, 105, 110, 100, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 65, 114, 103, 115, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0_value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 72, 67, 111, 110, 103, 114, 80, 114, 111, 111, 102, 39, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 110, 226, 130, 129, 46, 114, 111, 111, 116, 32, 110, 226, 130, 130, 46, 114, 111, 111, 116, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0_value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 69, 113, 80, 114, 111, 111, 102, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 69,
            113, 67, 111, 110, 103, 114, 83, 121, 109, 109, 80, 114, 111, 111, 102, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value: LeanStringObject<225> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 225,
        m_capacity: 225,
        m_length: 216,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101,
            97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110,
            100, 46, 80, 114, 111, 111, 102, 46, 49, 53, 50, 57, 49, 55, 50, 56, 51, 55, 46, 95,
            104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 57, 56, 48, 46, 48, 32, 41, 46,
            104, 97, 115, 83, 97, 109, 101, 82, 111, 111, 116, 32, 97, 226, 130, 129, 32, 98, 226,
            130, 130, 32, 38, 38, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64,
            46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114,
            105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 49, 53, 50, 57, 49, 55, 50, 56, 51, 55,
            46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 57, 56, 48, 46, 49, 32,
            41, 46, 104, 97, 115, 83, 97, 109, 101, 82, 111, 111, 116, 32, 98, 226, 130, 129, 32,
            97, 226, 130, 130, 10, 32, 32, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value: LeanStringObject<11> =
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
        m_data: [104, 101, 113, 95, 99, 111, 110, 103, 114, 39, 0],
    };
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__5_value)
                as *mut LeanObject,
            3236186592558201612 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7_value: LeanStringObject<10> =
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
        m_data: [101, 113, 95, 99, 111, 110, 103, 114, 39, 0],
    };
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7_value) as *mut LeanObject;
static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__7_value)
                as *mut LeanObject,
            14629152046939103435 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 109, 112, 108, 105, 101, 115, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__0_value) as *mut LeanObject,11074994739801900941 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2:
    u64 = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 67, 111, 110, 103, 114, 80, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 114, 104, 115, 46, 103, 101, 116, 65, 112, 112, 78, 117, 109, 65, 114, 103, 115, 32, 61, 61, 32, 110, 117, 109, 65, 114, 103, 115, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 114, 104, 115, 46, 103, 101, 116, 65, 112, 112, 78, 117, 109, 65, 114, 103, 115, 32, 61, 61, 32, 110, 117, 109, 65, 114, 103, 115, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0_value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 72, 67, 111, 110, 103, 114, 80, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqCongrProof___closed__0_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 69,
            113, 67, 111, 110, 103, 114, 80, 114, 111, 111, 102, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value: LeanStringObject<225> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 225,
        m_capacity: 225,
        m_length: 216,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101,
            97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110,
            100, 46, 80, 114, 111, 111, 102, 46, 49, 53, 50, 57, 49, 55, 50, 56, 51, 55, 46, 95,
            104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 53, 48, 50, 46, 48, 32, 41, 46,
            104, 97, 115, 83, 97, 109, 101, 82, 111, 111, 116, 32, 97, 226, 130, 129, 32, 97, 226,
            130, 130, 32, 38, 38, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64,
            46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114,
            105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 49, 53, 50, 57, 49, 55, 50, 56, 51, 55,
            46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 53, 48, 50, 46, 49, 32,
            41, 46, 104, 97, 115, 83, 97, 109, 101, 82, 111, 111, 116, 32, 98, 226, 130, 129, 32,
            98, 226, 130, 130, 10, 32, 32, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value: LeanStringObject<10> =
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
        m_data: [104, 101, 113, 95, 99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value) as *mut LeanObject;
static l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__5_value) as *mut LeanObject,
        13072361882825125162 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkEqCongrProof___closed__7_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [101, 113, 95, 99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__7_value) as *mut LeanObject;
static l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__7_value) as *mut LeanObject,
        7029998926428872175 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkEqCongrProof___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqCongrProof___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [110, 101, 115, 116, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value
) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__7_value) as *mut LeanObject,11081308864005098561 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [110, 101, 115, 116, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__2_value) as *mut LeanObject,9403212991100915159 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 101, 115, 116, 101, 100, 80, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value
) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__9_value) as *mut LeanObject,1862916703178820790 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [110, 101, 115, 116, 101, 100, 80, 114, 111, 111, 102, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__0_value) as *mut LeanObject,16712747556796397790 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0_value: LeanStringObject<66> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 80, 114, 111, 111, 102, 84, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 80, 114, 111, 111, 102, 70, 114, 111, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__3_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0_value: LeanStringObject<77> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 77, m_capacity: 77, m_length: 76, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 111, 102, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 67, 111, 110, 103, 114, 80, 114, 111, 111, 102, 70, 117, 110, 67, 67, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqProofImpl___closed__0_value: LeanStringObject<74> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 74,
        m_capacity: 74,
        m_length: 73,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 96, 103, 114, 105, 110, 100, 96, 32, 101,
            114, 114, 111, 114, 44, 32, 96, 109, 107, 69, 113, 80, 114, 111, 111, 102, 96, 32, 105,
            110, 118, 111, 107, 101, 100, 32, 119, 105, 116, 104, 32, 116, 101, 114, 109, 115, 32,
            111, 102, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 116, 121, 112, 101, 115,
            0,
        ],
    };
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqProofImpl___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqProofImpl___closed__2_value: LeanStringObject<10> =
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
        m_data: [10, 104, 97, 115, 32, 116, 121, 112, 101, 0],
    };
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqProofImpl___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkEqProofImpl___closed__4_value: LeanStringObject<5> =
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
        m_data: [10, 98, 117, 116, 0],
    };
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkEqProofImpl___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkEqProofImpl___closed__5: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(
    mut v_h_3103_: *mut LeanObject,
    mut v_a_3104_: *mut LeanObject,
    mut v_a_3105_: *mut LeanObject,
    mut v_a_3106_: *mut LeanObject,
    mut v_a_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3130_: u8 = 0;
    let mut v_a_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3107_);
                lean_inc_ref(v_a_3106_);
                lean_inc(v_a_3105_);
                lean_inc_ref(v_a_3104_);
                v___x_3109_ =
                    lean_infer_type(v_h_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
                if lean_obj_tag(v___x_3109_) == 0 {
                    v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
                    lean_inc(v_a_3110_);
                    lean_dec_ref_known(v___x_3109_, 1);
                    v___x_3111_ =
                        l_Lean_Meta_whnfD(v_a_3110_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
                    if lean_obj_tag(v___x_3111_) == 0 {
                        v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
                        v_isSharedCheck_3122_ = (!lean_is_exclusive(v___x_3111_)) as u8;
                        if v_isSharedCheck_3122_ == 0 {
                            v___x_3114_ = v___x_3111_;
                            v_isShared_3115_ = v_isSharedCheck_3122_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3112_);
                            lean_dec(v___x_3111_);
                            v___x_3114_ = lean_box(0);
                            v_isShared_3115_ = v_isSharedCheck_3122_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3123_ = lean_ctor_get(v___x_3111_, 0);
                        v_isSharedCheck_3130_ = (!lean_is_exclusive(v___x_3111_)) as u8;
                        if v_isSharedCheck_3130_ == 0 {
                            v___x_3125_ = v___x_3111_;
                            v_isShared_3126_ = v_isSharedCheck_3130_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3123_);
                            lean_dec(v___x_3111_);
                            v___x_3125_ = lean_box(0);
                            v_isShared_3126_ = v_isSharedCheck_3130_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_3131_ = lean_ctor_get(v___x_3109_, 0);
                    v_isSharedCheck_3138_ = (!lean_is_exclusive(v___x_3109_)) as u8;
                    if v_isSharedCheck_3138_ == 0 {
                        v___x_3133_ = v___x_3109_;
                        v_isShared_3134_ = v_isSharedCheck_3138_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3131_);
                        lean_dec(v___x_3109_);
                        v___x_3133_ = lean_box(0);
                        v_isShared_3134_ = v_isSharedCheck_3138_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3116_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1;
                v___x_3117_ = l_Lean_Expr_isAppOf(v_a_3112_, v___x_3116_);
                lean_dec(v_a_3112_);
                v___x_3118_ = lean_box((v___x_3117_) as usize);
                if v_isShared_3115_ == 0 {
                    lean_ctor_set(v___x_3114_, 0, v___x_3118_);
                    v___x_3120_ = v___x_3114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
                    v___x_3120_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3120_;
            }
            3 => {
                if v_isShared_3126_ == 0 {
                    v___x_3128_ = v___x_3125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
                    v___x_3128_ = v_reuseFailAlloc_3129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3128_;
            }
            5 => {
                if v_isShared_3134_ == 0 {
                    v___x_3136_ = v___x_3133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
                    v___x_3136_ = v_reuseFailAlloc_3137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___boxed(
    mut v_h_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3145_: *mut LeanObject = core::ptr::null_mut();
    v_res_3145_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(
        v_h_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_,
    );
    lean_dec(v_a_3143_);
    lean_dec_ref(v_a_3142_);
    lean_dec(v_a_3141_);
    lean_dec_ref(v_a_3140_);
    return v_res_3145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(
    mut v_a_3146_: *mut LeanObject,
    mut v_b_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v_fst_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3171_: u8 = 0;
    let mut v_isSharedCheck_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3174_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_a_3146_, v_b_3147_,
                    );
                if v___x_3174_ == 0 {
                    v___x_3175_ = l_Lean_Expr_isApp(v_a_3146_);
                    if v___x_3175_ == 0 {
                        v___y_3149_ = v___x_3175_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3176_ = l_Lean_Expr_isApp(v_b_3147_);
                        v___y_3149_ = v___x_3176_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3177_ = lean_unsigned_to_nat(0);
                    v___x_3178_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3178_, 0, v_a_3146_);
                    lean_ctor_set(v___x_3178_, 1, v___x_3177_);
                    v___x_3179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3179_, 0, v___x_3178_);
                    return v___x_3179_;
                }
            }
            1 => {
                if v___y_3149_ == 0 {
                    lean_dec_ref(v_a_3146_);
                    v___x_3150_ = lean_box(0);
                    return v___x_3150_;
                } else {
                    v___x_3151_ = l_Lean_Expr_appFn_x21(v_a_3146_);
                    lean_dec_ref(v_a_3146_);
                    v___x_3152_ = l_Lean_Expr_appFn_x21(v_b_3147_);
                    v___x_3153_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v___x_3151_, v___x_3152_);
                    lean_dec_ref(v___x_3152_);
                    if lean_obj_tag(v___x_3153_) == 1 {
                        v_val_3154_ = lean_ctor_get(v___x_3153_, 0);
                        v_isSharedCheck_3172_ = (!lean_is_exclusive(v___x_3153_)) as u8;
                        if v_isSharedCheck_3172_ == 0 {
                            v___x_3156_ = v___x_3153_;
                            v_isShared_3157_ = v_isSharedCheck_3172_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_3154_);
                            lean_dec(v___x_3153_);
                            v___x_3156_ = lean_box(0);
                            v_isShared_3157_ = v_isSharedCheck_3172_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3153_);
                        v___x_3173_ = lean_box(0);
                        return v___x_3173_;
                    }
                }
            }
            2 => {
                v_fst_3158_ = lean_ctor_get(v_val_3154_, 0);
                v_snd_3159_ = lean_ctor_get(v_val_3154_, 1);
                v_isSharedCheck_3171_ = (!lean_is_exclusive(v_val_3154_)) as u8;
                if v_isSharedCheck_3171_ == 0 {
                    v___x_3161_ = v_val_3154_;
                    v_isShared_3162_ = v_isSharedCheck_3171_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3159_);
                    lean_inc(v_fst_3158_);
                    lean_dec(v_val_3154_);
                    v___x_3161_ = lean_box(0);
                    v_isShared_3162_ = v_isSharedCheck_3171_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3163_ = lean_unsigned_to_nat(1);
                v___x_3164_ = lean_nat_add(v_snd_3159_, v___x_3163_);
                lean_dec(v_snd_3159_);
                if v_isShared_3162_ == 0 {
                    lean_ctor_set(v___x_3161_, 1, v___x_3164_);
                    v___x_3166_ = v___x_3161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_fst_3158_);
                    lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3164_);
                    v___x_3166_ = v_reuseFailAlloc_3170_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3157_ == 0 {
                    lean_ctor_set(v___x_3156_, 0, v___x_3166_);
                    v___x_3168_ = v___x_3156_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
                    v___x_3168_ = v_reuseFailAlloc_3169_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix___boxed(
    mut v_a_3180_: *mut LeanObject,
    mut v_b_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3182_: *mut LeanObject = core::ptr::null_mut();
    v_res_3182_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(
        v_a_3180_, v_b_3181_,
    );
    lean_dec_ref(v_b_3181_);
    return v_res_3182_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(
    mut v_h_3183_: *mut LeanObject,
    mut v_flipped_3184_: u8,
    mut v_heq_3185_: u8,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v_a_3188_: *mut LeanObject,
    mut v_a_3189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h_x27_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_heq_3185_ == 0 {
                    v_h_x27_3192_ = v_h_3183_;
                    v___y_3193_ = v_a_3186_;
                    v___y_3194_ = v_a_3187_;
                    v___y_3195_ = v_a_3188_;
                    v___y_3196_ = v_a_3189_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_h_3183_);
                    v___x_3200_ =
                        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof(
                            v_h_3183_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_,
                        );
                    if lean_obj_tag(v___x_3200_) == 0 {
                        v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
                        lean_inc(v_a_3201_);
                        lean_dec_ref_known(v___x_3200_, 1);
                        v___x_3202_ = (lean_unbox(v_a_3201_) as u8);
                        lean_dec(v_a_3201_);
                        if v___x_3202_ == 0 {
                            v_h_x27_3192_ = v_h_3183_;
                            v___y_3193_ = v_a_3186_;
                            v___y_3194_ = v_a_3187_;
                            v___y_3195_ = v_a_3188_;
                            v___y_3196_ = v_a_3189_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3203_ = l_Lean_Meta_mkHEqOfEq(
                                v_h_3183_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_,
                            );
                            if lean_obj_tag(v___x_3203_) == 0 {
                                v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
                                lean_inc(v_a_3204_);
                                lean_dec_ref_known(v___x_3203_, 1);
                                v_h_x27_3192_ = v_a_3204_;
                                v___y_3193_ = v_a_3186_;
                                v___y_3194_ = v_a_3187_;
                                v___y_3195_ = v_a_3188_;
                                v___y_3196_ = v_a_3189_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_3203_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_h_3183_);
                        v_a_3205_ = lean_ctor_get(v___x_3200_, 0);
                        v_isSharedCheck_3212_ = (!lean_is_exclusive(v___x_3200_)) as u8;
                        if v_isSharedCheck_3212_ == 0 {
                            v___x_3207_ = v___x_3200_;
                            v_isShared_3208_ = v_isSharedCheck_3212_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3205_);
                            lean_dec(v___x_3200_);
                            v___x_3207_ = lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3212_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_flipped_3184_ == 0 {
                    v___x_3197_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3197_, 0, v_h_x27_3192_);
                    return v___x_3197_;
                } else {
                    if v_heq_3185_ == 0 {
                        v___x_3198_ = l_Lean_Meta_mkEqSymm(
                            v_h_x27_3192_,
                            v___y_3193_,
                            v___y_3194_,
                            v___y_3195_,
                            v___y_3196_,
                        );
                        return v___x_3198_;
                    } else {
                        v___x_3199_ = l_Lean_Meta_mkHEqSymm(
                            v_h_x27_3192_,
                            v___y_3193_,
                            v___y_3194_,
                            v___y_3195_,
                            v___y_3196_,
                        );
                        return v___x_3199_;
                    }
                }
            }
            2 => {
                if v_isShared_3208_ == 0 {
                    v___x_3210_ = v___x_3207_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
                    v___x_3210_ = v_reuseFailAlloc_3211_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof___boxed(
    mut v_h_3213_: *mut LeanObject,
    mut v_flipped_3214_: *mut LeanObject,
    mut v_heq_3215_: *mut LeanObject,
    mut v_a_3216_: *mut LeanObject,
    mut v_a_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
    mut v_a_3220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flipped_boxed_3221_: u8 = 0;
    let mut v_heq_boxed_3222_: u8 = 0;
    let mut v_res_3223_: *mut LeanObject = core::ptr::null_mut();
    v_flipped_boxed_3221_ = (lean_unbox(v_flipped_3214_) as u8);
    v_heq_boxed_3222_ = (lean_unbox(v_heq_3215_) as u8);
    v_res_3223_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(
        v_h_3213_,
        v_flipped_boxed_3221_,
        v_heq_boxed_3222_,
        v_a_3216_,
        v_a_3217_,
        v_a_3218_,
        v_a_3219_,
    );
    lean_dec(v_a_3219_);
    lean_dec_ref(v_a_3218_);
    lean_dec(v_a_3217_);
    lean_dec_ref(v_a_3216_);
    return v_res_3223_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(
    mut v_a_3224_: *mut LeanObject,
    mut v_heq_3225_: u8,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
) -> *mut LeanObject {
    if v_heq_3225_ == 0 {
        let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
        v___x_3231_ = l_Lean_Meta_mkEqRefl(v_a_3224_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
        return v___x_3231_;
    } else {
        let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
        v___x_3232_ = l_Lean_Meta_mkHEqRefl(v_a_3224_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
        return v___x_3232_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl___boxed(
    mut v_a_3233_: *mut LeanObject,
    mut v_heq_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_3240_: u8 = 0;
    let mut v_res_3241_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_3240_ = (lean_unbox(v_heq_3234_) as u8);
    v_res_3241_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(
        v_a_3233_,
        v_heq_boxed_3240_,
        v_a_3235_,
        v_a_3236_,
        v_a_3237_,
        v_a_3238_,
    );
    lean_dec(v_a_3238_);
    lean_dec_ref(v_a_3237_);
    lean_dec(v_a_3236_);
    lean_dec_ref(v_a_3235_);
    return v_res_3241_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(
    mut v_h_u2081_3242_: *mut LeanObject,
    mut v_h_u2082_3243_: *mut LeanObject,
    mut v_heq_3244_: u8,
    mut v_a_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
    mut v_a_3248_: *mut LeanObject,
) -> *mut LeanObject {
    if v_heq_3244_ == 0 {
        let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
        v___x_3250_ = l_Lean_Meta_mkEqTrans(
            v_h_u2081_3242_,
            v_h_u2082_3243_,
            v_a_3245_,
            v_a_3246_,
            v_a_3247_,
            v_a_3248_,
        );
        return v___x_3250_;
    } else {
        let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
        v___x_3251_ = l_Lean_Meta_mkHEqTrans(
            v_h_u2081_3242_,
            v_h_u2082_3243_,
            v_a_3245_,
            v_a_3246_,
            v_a_3247_,
            v_a_3248_,
        );
        return v___x_3251_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans___boxed(
    mut v_h_u2081_3252_: *mut LeanObject,
    mut v_h_u2082_3253_: *mut LeanObject,
    mut v_heq_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
    mut v_a_3256_: *mut LeanObject,
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_3260_: u8 = 0;
    let mut v_res_3261_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_3260_ = (lean_unbox(v_heq_3254_) as u8);
    v_res_3261_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(
        v_h_u2081_3252_,
        v_h_u2082_3253_,
        v_heq_boxed_3260_,
        v_a_3255_,
        v_a_3256_,
        v_a_3257_,
        v_a_3258_,
    );
    lean_dec(v_a_3258_);
    lean_dec_ref(v_a_3257_);
    lean_dec(v_a_3256_);
    lean_dec_ref(v_a_3255_);
    return v_res_3261_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(
    mut v_h_u2081_3262_: *mut LeanObject,
    mut v_h_u2082_3263_: *mut LeanObject,
    mut v_heq_3264_: u8,
    mut v_a_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_h_u2081_3262_) == 1 {
        let mut v_val_3270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
        v_val_3270_ = lean_ctor_get(v_h_u2081_3262_, 0);
        lean_inc(v_val_3270_);
        lean_dec_ref_known(v_h_u2081_3262_, 1);
        v___x_3271_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans(
            v_val_3270_,
            v_h_u2082_3263_,
            v_heq_3264_,
            v_a_3265_,
            v_a_3266_,
            v_a_3267_,
            v_a_3268_,
        );
        return v___x_3271_;
    } else {
        let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h_u2081_3262_);
        v___x_3272_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3272_, 0, v_h_u2082_3263_);
        return v___x_3272_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27___boxed(
    mut v_h_u2081_3273_: *mut LeanObject,
    mut v_h_u2082_3274_: *mut LeanObject,
    mut v_heq_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
    mut v_a_3279_: *mut LeanObject,
    mut v_a_3280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_3281_: u8 = 0;
    let mut v_res_3282_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_3281_ = (lean_unbox(v_heq_3275_) as u8);
    v_res_3282_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(
        v_h_u2081_3273_,
        v_h_u2082_3274_,
        v_heq_boxed_3281_,
        v_a_3276_,
        v_a_3277_,
        v_a_3278_,
        v_a_3279_,
    );
    lean_dec(v_a_3279_);
    lean_dec_ref(v_a_3278_);
    lean_dec(v_a_3277_);
    lean_dec_ref(v_a_3276_);
    return v_res_3282_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(
    mut v_h_3283_: *mut LeanObject,
    mut v_heq_3284_: u8,
    mut v_a_3285_: *mut LeanObject,
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
) -> *mut LeanObject {
    if v_heq_3284_ == 0 {
        let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
        v___x_3290_ = l_Lean_Meta_mkEqOfHEq(
            v_h_3283_,
            v_heq_3284_,
            v_a_3285_,
            v_a_3286_,
            v_a_3287_,
            v_a_3288_,
        );
        return v___x_3290_;
    } else {
        let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
        v___x_3291_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3291_, 0, v_h_3283_);
        return v___x_3291_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded___boxed(
    mut v_h_3292_: *mut LeanObject,
    mut v_heq_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
    mut v_a_3295_: *mut LeanObject,
    mut v_a_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_3299_: u8 = 0;
    let mut v_res_3300_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_3299_ = (lean_unbox(v_heq_3293_) as u8);
    v_res_3300_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(
        v_h_3292_,
        v_heq_boxed_3299_,
        v_a_3294_,
        v_a_3295_,
        v_a_3296_,
        v_a_3297_,
    );
    lean_dec(v_a_3297_);
    lean_dec_ref(v_a_3296_);
    lean_dec(v_a_3295_);
    lean_dec_ref(v_a_3294_);
    return v_res_3300_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_3301_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(
    mut v_msg_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_12097__overap_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___closed__0);
    v___x_12097__overap_3315_ = lean_panic_fn_borrowed(v___x_3314_, v_msg_3302_);
    lean_inc(v___y_3312_);
    lean_inc_ref(v___y_3311_);
    lean_inc(v___y_3310_);
    lean_inc_ref(v___y_3309_);
    lean_inc(v___y_3308_);
    lean_inc_ref(v___y_3307_);
    lean_inc(v___y_3306_);
    lean_inc_ref(v___y_3305_);
    lean_inc(v___y_3304_);
    lean_inc(v___y_3303_);
    v___x_3316_ = lean_apply_11(
        v___x_12097__overap_3315_,
        v___y_3303_,
        v___y_3304_,
        v___y_3305_,
        v___y_3306_,
        v___y_3307_,
        v___y_3308_,
        v___y_3309_,
        v___y_3310_,
        v___y_3311_,
        v___y_3312_,
        lean_box(0),
    );
    return v___x_3316_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3___boxed(
    mut v_msg_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3329_: *mut LeanObject = core::ptr::null_mut();
    v_res_3329_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v_msg_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    lean_dec(v___y_3325_);
    lean_dec_ref(v___y_3324_);
    lean_dec(v___y_3323_);
    lean_dec_ref(v___y_3322_);
    lean_dec(v___y_3321_);
    lean_dec_ref(v___y_3320_);
    lean_dec(v___y_3319_);
    lean_dec(v___y_3318_);
    return v_res_3329_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_3330_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(
    mut v_msg_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_12895__overap_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v___x_3343_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___closed__0);
    v___x_12895__overap_3344_ = lean_panic_fn_borrowed(v___x_3343_, v_msg_3331_);
    lean_inc(v___y_3341_);
    lean_inc_ref(v___y_3340_);
    lean_inc(v___y_3339_);
    lean_inc_ref(v___y_3338_);
    lean_inc(v___y_3337_);
    lean_inc_ref(v___y_3336_);
    lean_inc(v___y_3335_);
    lean_inc_ref(v___y_3334_);
    lean_inc(v___y_3333_);
    lean_inc(v___y_3332_);
    v___x_3345_ = lean_apply_11(
        v___x_12895__overap_3344_,
        v___y_3332_,
        v___y_3333_,
        v___y_3334_,
        v___y_3335_,
        v___y_3336_,
        v___y_3337_,
        v___y_3338_,
        v___y_3339_,
        v___y_3340_,
        v___y_3341_,
        lean_box(0),
    );
    return v___x_3345_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5___boxed(
    mut v_msg_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3358_: *mut LeanObject = core::ptr::null_mut();
    v_res_3358_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v_msg_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
    lean_dec(v___y_3356_);
    lean_dec_ref(v___y_3355_);
    lean_dec(v___y_3354_);
    lean_dec_ref(v___y_3353_);
    lean_dec(v___y_3352_);
    lean_dec_ref(v___y_3351_);
    lean_dec(v___y_3350_);
    lean_dec_ref(v___y_3349_);
    lean_dec(v___y_3348_);
    lean_dec(v___y_3347_);
    return v_res_3358_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(
    mut v_t_3359_: *mut LeanObject,
    mut v_k_3360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3359_) == 0 {
                    v_k_3361_ = lean_ctor_get(v_t_3359_, 1);
                    v_v_3362_ = lean_ctor_get(v_t_3359_, 2);
                    v_l_3363_ = lean_ctor_get(v_t_3359_, 3);
                    v_r_3364_ = lean_ctor_get(v_t_3359_, 4);
                    v___x_3365_ = lean_nat_dec_lt(v_k_3360_, v_k_3361_);
                    if v___x_3365_ == 0 {
                        v___x_3366_ = lean_nat_dec_eq(v_k_3360_, v_k_3361_);
                        if v___x_3366_ == 0 {
                            v_t_3359_ = v_r_3364_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_v_3362_);
                            v___x_3368_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3368_, 0, v_v_3362_);
                            return v___x_3368_;
                        }
                    } else {
                        v_t_3359_ = v_l_3363_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_3370_ = lean_box(0);
                    return v___x_3370_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg___boxed(
    mut v_t_3371_: *mut LeanObject,
    mut v_k_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3373_: *mut LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_3371_, v_k_3372_);
    lean_dec(v_k_3372_);
    lean_dec(v_t_3371_);
    return v_res_3373_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    v___x_3377_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_3378_ = lean_unsigned_to_nat(35);
    v___x_3379_ = lean_unsigned_to_nat(87);
    v___x_3380_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1;
    v___x_3381_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_3382_ = l_mkPanicMessageWithDecl(
        v___x_3381_,
        v___x_3380_,
        v___x_3379_,
        v___x_3378_,
        v___x_3377_,
    );
    return v___x_3382_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(
    mut v___x_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3405_: u8 = 0;
    let mut v_target_x3f_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_unused_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3396_ = lean_st_ref_get(v___y_3385_);
                v_snd_3397_ = lean_ctor_get(v_a_3384_, 1);
                v_isSharedCheck_3444_ = (!lean_is_exclusive(v_a_3384_)) as u8;
                if v_isSharedCheck_3444_ == 0 {
                    v_unused_3445_ = lean_ctor_get(v_a_3384_, 0);
                    lean_dec(v_unused_3445_);
                    v___x_3399_ = v_a_3384_;
                    v_isShared_3400_ = v_isSharedCheck_3444_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3397_);
                    lean_dec(v_a_3384_);
                    v___x_3399_ = lean_box(0);
                    v_isShared_3400_ = v_isSharedCheck_3444_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_3397_);
                v___x_3401_ = l_Lean_Meta_Grind_Goal_getENode(
                    v___x_3396_,
                    v_snd_3397_,
                    v___y_3391_,
                    v___y_3392_,
                    v___y_3393_,
                    v___y_3394_,
                );
                lean_dec(v___x_3396_);
                if lean_obj_tag(v___x_3401_) == 0 {
                    v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
                    v_isSharedCheck_3435_ = (!lean_is_exclusive(v___x_3401_)) as u8;
                    if v_isSharedCheck_3435_ == 0 {
                        v___x_3404_ = v___x_3401_;
                        v_isShared_3405_ = v_isSharedCheck_3435_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3402_);
                        lean_dec(v___x_3401_);
                        v___x_3404_ = lean_box(0);
                        v_isShared_3405_ = v_isSharedCheck_3435_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3399_);
                    lean_dec(v_snd_3397_);
                    v_a_3436_ = lean_ctor_get(v___x_3401_, 0);
                    v_isSharedCheck_3443_ = (!lean_is_exclusive(v___x_3401_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v___x_3438_ = v___x_3401_;
                        v_isShared_3439_ = v_isSharedCheck_3443_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3436_);
                        lean_dec(v___x_3401_);
                        v___x_3438_ = lean_box(0);
                        v_isShared_3439_ = v_isSharedCheck_3443_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_target_x3f_3406_ = lean_ctor_get(v_a_3402_, 4);
                lean_inc(v_target_x3f_3406_);
                v_idx_3407_ = lean_ctor_get(v_a_3402_, 7);
                lean_inc(v_idx_3407_);
                lean_dec(v_a_3402_);
                v___x_3408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v___x_3383_, v_idx_3407_);
                lean_dec(v_idx_3407_);
                if lean_obj_tag(v___x_3408_) == 1 {
                    lean_dec(v_target_x3f_3406_);
                    if v_isShared_3400_ == 0 {
                        lean_ctor_set(v___x_3399_, 0, v___x_3408_);
                        v___x_3410_ = v___x_3399_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3408_);
                        lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_snd_3397_);
                        v___x_3410_ = v_reuseFailAlloc_3414_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3408_);
                    lean_del_object(v___x_3404_);
                    v___x_3415_ = lean_box(0);
                    if lean_obj_tag(v_target_x3f_3406_) == 1 {
                        lean_dec(v_snd_3397_);
                        v_val_3416_ = lean_ctor_get(v_target_x3f_3406_, 0);
                        lean_inc(v_val_3416_);
                        lean_dec_ref_known(v_target_x3f_3406_, 1);
                        if v_isShared_3400_ == 0 {
                            lean_ctor_set(v___x_3399_, 1, v_val_3416_);
                            lean_ctor_set(v___x_3399_, 0, v___x_3415_);
                            v___x_3418_ = v___x_3399_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3415_);
                            lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_val_3416_);
                            v___x_3418_ = v_reuseFailAlloc_3420_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_target_x3f_3406_);
                        v___x_3421_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__3);
                        v___x_3422_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__3(v___x_3421_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
                        if lean_obj_tag(v___x_3422_) == 0 {
                            lean_dec_ref_known(v___x_3422_, 1);
                            if v_isShared_3400_ == 0 {
                                lean_ctor_set(v___x_3399_, 0, v___x_3415_);
                                v___x_3424_ = v___x_3399_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3415_);
                                lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_snd_3397_);
                                v___x_3424_ = v_reuseFailAlloc_3426_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3399_);
                            lean_dec(v_snd_3397_);
                            v_a_3427_ = lean_ctor_get(v___x_3422_, 0);
                            v_isSharedCheck_3434_ = (!lean_is_exclusive(v___x_3422_)) as u8;
                            if v_isSharedCheck_3434_ == 0 {
                                v___x_3429_ = v___x_3422_;
                                v_isShared_3430_ = v_isSharedCheck_3434_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3427_);
                                lean_dec(v___x_3422_);
                                v___x_3429_ = lean_box(0);
                                v_isShared_3430_ = v_isSharedCheck_3434_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3405_ == 0 {
                    lean_ctor_set(v___x_3404_, 0, v___x_3410_);
                    v___x_3412_ = v___x_3404_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
                    v___x_3412_ = v_reuseFailAlloc_3413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3412_;
            }
            5 => {
                v_a_3384_ = v___x_3418_;
                state = 0;
                continue;
            }
            6 => {
                v_a_3384_ = v___x_3424_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_3430_ == 0 {
                    v___x_3432_ = v___x_3429_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
                    v___x_3432_ = v_reuseFailAlloc_3433_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3432_;
            }
            9 => {
                if v_isShared_3439_ == 0 {
                    v___x_3441_ = v___x_3438_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
                    v___x_3441_ = v_reuseFailAlloc_3442_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___boxed(
    mut v___x_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
    mut v___y_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3459_: *mut LeanObject = core::ptr::null_mut();
    v_res_3459_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_3446_, v_a_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
    lean_dec(v___y_3457_);
    lean_dec_ref(v___y_3456_);
    lean_dec(v___y_3455_);
    lean_dec_ref(v___y_3454_);
    lean_dec(v___y_3453_);
    lean_dec_ref(v___y_3452_);
    lean_dec(v___y_3451_);
    lean_dec_ref(v___y_3450_);
    lean_dec(v___y_3449_);
    lean_dec(v___y_3448_);
    lean_dec(v___x_3446_);
    return v_res_3459_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(
    mut v_k_3460_: *mut LeanObject,
    mut v_v_3461_: *mut LeanObject,
    mut v_t_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3470_: u8 = 0;
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: u8 = 0;
    let mut v_impl_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3491_: u8 = 0;
    let mut v_size_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_unused_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut v_unused_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut v_unused_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v_k_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_unused_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_unused_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_unused_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: u8 = 0;
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v_size_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v_unused_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_unused_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_unused_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v_unused_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v_k_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v_unused_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut v_unused_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3462_) == 0 {
                    v_size_3463_ = lean_ctor_get(v_t_3462_, 0);
                    v_k_3464_ = lean_ctor_get(v_t_3462_, 1);
                    v_v_3465_ = lean_ctor_get(v_t_3462_, 2);
                    v_l_3466_ = lean_ctor_get(v_t_3462_, 3);
                    v_r_3467_ = lean_ctor_get(v_t_3462_, 4);
                    v_isSharedCheck_3748_ = (!lean_is_exclusive(v_t_3462_)) as u8;
                    if v_isSharedCheck_3748_ == 0 {
                        v___x_3469_ = v_t_3462_;
                        v_isShared_3470_ = v_isSharedCheck_3748_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3467_);
                        lean_inc(v_l_3466_);
                        lean_inc(v_v_3465_);
                        lean_inc(v_k_3464_);
                        lean_inc(v_size_3463_);
                        lean_dec(v_t_3462_);
                        v___x_3469_ = lean_box(0);
                        v_isShared_3470_ = v_isSharedCheck_3748_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3749_ = lean_unsigned_to_nat(1);
                    v___x_3750_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3750_, 0, v___x_3749_);
                    lean_ctor_set(v___x_3750_, 1, v_k_3460_);
                    lean_ctor_set(v___x_3750_, 2, v_v_3461_);
                    lean_ctor_set(v___x_3750_, 3, v_t_3462_);
                    lean_ctor_set(v___x_3750_, 4, v_t_3462_);
                    return v___x_3750_;
                }
            }
            1 => {
                v___x_3471_ = lean_nat_dec_lt(v_k_3460_, v_k_3464_);
                if v___x_3471_ == 0 {
                    v___x_3472_ = lean_nat_dec_eq(v_k_3460_, v_k_3464_);
                    if v___x_3472_ == 0 {
                        lean_dec(v_size_3463_);
                        v_impl_3473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_3460_, v_v_3461_, v_r_3467_);
                        v___x_3474_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_3466_) == 0 {
                            v_size_3475_ = lean_ctor_get(v_l_3466_, 0);
                            v_size_3476_ = lean_ctor_get(v_impl_3473_, 0);
                            lean_inc(v_size_3476_);
                            v_k_3477_ = lean_ctor_get(v_impl_3473_, 1);
                            lean_inc(v_k_3477_);
                            v_v_3478_ = lean_ctor_get(v_impl_3473_, 2);
                            lean_inc(v_v_3478_);
                            v_l_3479_ = lean_ctor_get(v_impl_3473_, 3);
                            lean_inc(v_l_3479_);
                            v_r_3480_ = lean_ctor_get(v_impl_3473_, 4);
                            lean_inc(v_r_3480_);
                            v___x_3481_ = lean_unsigned_to_nat(3);
                            v___x_3482_ = lean_nat_mul(v___x_3481_, v_size_3475_);
                            v___x_3483_ = lean_nat_dec_lt(v___x_3482_, v_size_3476_);
                            lean_dec(v___x_3482_);
                            if v___x_3483_ == 0 {
                                lean_dec(v_r_3480_);
                                lean_dec(v_l_3479_);
                                lean_dec(v_v_3478_);
                                lean_dec(v_k_3477_);
                                v___x_3484_ = lean_nat_add(v___x_3474_, v_size_3475_);
                                v___x_3485_ = lean_nat_add(v___x_3484_, v_size_3476_);
                                lean_dec(v_size_3476_);
                                lean_dec(v___x_3484_);
                                if v_isShared_3470_ == 0 {
                                    lean_ctor_set(v___x_3469_, 4, v_impl_3473_);
                                    lean_ctor_set(v___x_3469_, 0, v___x_3485_);
                                    v___x_3487_ = v___x_3469_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                                    lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_k_3464_);
                                    lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_v_3465_);
                                    lean_ctor_set(v_reuseFailAlloc_3488_, 3, v_l_3466_);
                                    lean_ctor_set(v_reuseFailAlloc_3488_, 4, v_impl_3473_);
                                    v___x_3487_ = v_reuseFailAlloc_3488_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3552_ = (!lean_is_exclusive(v_impl_3473_)) as u8;
                                if v_isSharedCheck_3552_ == 0 {
                                    v_unused_3553_ = lean_ctor_get(v_impl_3473_, 4);
                                    lean_dec(v_unused_3553_);
                                    v_unused_3554_ = lean_ctor_get(v_impl_3473_, 3);
                                    lean_dec(v_unused_3554_);
                                    v_unused_3555_ = lean_ctor_get(v_impl_3473_, 2);
                                    lean_dec(v_unused_3555_);
                                    v_unused_3556_ = lean_ctor_get(v_impl_3473_, 1);
                                    lean_dec(v_unused_3556_);
                                    v_unused_3557_ = lean_ctor_get(v_impl_3473_, 0);
                                    lean_dec(v_unused_3557_);
                                    v___x_3490_ = v_impl_3473_;
                                    v_isShared_3491_ = v_isSharedCheck_3552_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3473_);
                                    v___x_3490_ = lean_box(0);
                                    v_isShared_3491_ = v_isSharedCheck_3552_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3558_ = lean_ctor_get(v_impl_3473_, 3);
                            lean_inc(v_l_3558_);
                            if lean_obj_tag(v_l_3558_) == 0 {
                                v_r_3559_ = lean_ctor_get(v_impl_3473_, 4);
                                v_k_3560_ = lean_ctor_get(v_impl_3473_, 1);
                                v_v_3561_ = lean_ctor_get(v_impl_3473_, 2);
                                v_isSharedCheck_3584_ = (!lean_is_exclusive(v_impl_3473_)) as u8;
                                if v_isSharedCheck_3584_ == 0 {
                                    v_unused_3585_ = lean_ctor_get(v_impl_3473_, 3);
                                    lean_dec(v_unused_3585_);
                                    v_unused_3586_ = lean_ctor_get(v_impl_3473_, 0);
                                    lean_dec(v_unused_3586_);
                                    v___x_3563_ = v_impl_3473_;
                                    v_isShared_3564_ = v_isSharedCheck_3584_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_3559_);
                                    lean_inc(v_v_3561_);
                                    lean_inc(v_k_3560_);
                                    lean_dec(v_impl_3473_);
                                    v___x_3563_ = lean_box(0);
                                    v_isShared_3564_ = v_isSharedCheck_3584_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3587_ = lean_ctor_get(v_impl_3473_, 4);
                                lean_inc(v_r_3587_);
                                if lean_obj_tag(v_r_3587_) == 0 {
                                    v_k_3588_ = lean_ctor_get(v_impl_3473_, 1);
                                    v_v_3589_ = lean_ctor_get(v_impl_3473_, 2);
                                    v_isSharedCheck_3600_ =
                                        (!lean_is_exclusive(v_impl_3473_)) as u8;
                                    if v_isSharedCheck_3600_ == 0 {
                                        v_unused_3601_ = lean_ctor_get(v_impl_3473_, 4);
                                        lean_dec(v_unused_3601_);
                                        v_unused_3602_ = lean_ctor_get(v_impl_3473_, 3);
                                        lean_dec(v_unused_3602_);
                                        v_unused_3603_ = lean_ctor_get(v_impl_3473_, 0);
                                        lean_dec(v_unused_3603_);
                                        v___x_3591_ = v_impl_3473_;
                                        v_isShared_3592_ = v_isSharedCheck_3600_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3589_);
                                        lean_inc(v_k_3588_);
                                        lean_dec(v_impl_3473_);
                                        v___x_3591_ = lean_box(0);
                                        v_isShared_3592_ = v_isSharedCheck_3600_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_3604_ = lean_unsigned_to_nat(2);
                                    if v_isShared_3470_ == 0 {
                                        lean_ctor_set(v___x_3469_, 4, v_impl_3473_);
                                        lean_ctor_set(v___x_3469_, 3, v_r_3587_);
                                        lean_ctor_set(v___x_3469_, 0, v___x_3604_);
                                        v___x_3606_ = v___x_3469_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
                                        lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3464_);
                                        lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3465_);
                                        lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_r_3587_);
                                        lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_impl_3473_);
                                        v___x_3606_ = v_reuseFailAlloc_3607_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_3465_);
                        lean_dec(v_k_3464_);
                        if v_isShared_3470_ == 0 {
                            lean_ctor_set(v___x_3469_, 2, v_v_3461_);
                            lean_ctor_set(v___x_3469_, 1, v_k_3460_);
                            v___x_3609_ = v___x_3469_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_size_3463_);
                            lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3460_);
                            lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3461_);
                            lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_l_3466_);
                            lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_r_3467_);
                            v___x_3609_ = v_reuseFailAlloc_3610_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_3463_);
                    v_impl_3611_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_3460_, v_v_3461_, v_l_3466_);
                    v___x_3612_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_3467_) == 0 {
                        v_size_3613_ = lean_ctor_get(v_r_3467_, 0);
                        v_size_3614_ = lean_ctor_get(v_impl_3611_, 0);
                        lean_inc(v_size_3614_);
                        v_k_3615_ = lean_ctor_get(v_impl_3611_, 1);
                        lean_inc(v_k_3615_);
                        v_v_3616_ = lean_ctor_get(v_impl_3611_, 2);
                        lean_inc(v_v_3616_);
                        v_l_3617_ = lean_ctor_get(v_impl_3611_, 3);
                        lean_inc(v_l_3617_);
                        v_r_3618_ = lean_ctor_get(v_impl_3611_, 4);
                        lean_inc(v_r_3618_);
                        v___x_3619_ = lean_unsigned_to_nat(3);
                        v___x_3620_ = lean_nat_mul(v___x_3619_, v_size_3613_);
                        v___x_3621_ = lean_nat_dec_lt(v___x_3620_, v_size_3614_);
                        lean_dec(v___x_3620_);
                        if v___x_3621_ == 0 {
                            lean_dec(v_r_3618_);
                            lean_dec(v_l_3617_);
                            lean_dec(v_v_3616_);
                            lean_dec(v_k_3615_);
                            v___x_3622_ = lean_nat_add(v___x_3612_, v_size_3614_);
                            lean_dec(v_size_3614_);
                            v___x_3623_ = lean_nat_add(v___x_3622_, v_size_3613_);
                            lean_dec(v___x_3622_);
                            if v_isShared_3470_ == 0 {
                                lean_ctor_set(v___x_3469_, 3, v_impl_3611_);
                                lean_ctor_set(v___x_3469_, 0, v___x_3623_);
                                v___x_3625_ = v___x_3469_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
                                lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3464_);
                                lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3465_);
                                lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_impl_3611_);
                                lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_r_3467_);
                                v___x_3625_ = v_reuseFailAlloc_3626_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_3692_ = (!lean_is_exclusive(v_impl_3611_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v_unused_3693_ = lean_ctor_get(v_impl_3611_, 4);
                                lean_dec(v_unused_3693_);
                                v_unused_3694_ = lean_ctor_get(v_impl_3611_, 3);
                                lean_dec(v_unused_3694_);
                                v_unused_3695_ = lean_ctor_get(v_impl_3611_, 2);
                                lean_dec(v_unused_3695_);
                                v_unused_3696_ = lean_ctor_get(v_impl_3611_, 1);
                                lean_dec(v_unused_3696_);
                                v_unused_3697_ = lean_ctor_get(v_impl_3611_, 0);
                                lean_dec(v_unused_3697_);
                                v___x_3628_ = v_impl_3611_;
                                v_isShared_3629_ = v_isSharedCheck_3692_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_3611_);
                                v___x_3628_ = lean_box(0);
                                v_isShared_3629_ = v_isSharedCheck_3692_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_3698_ = lean_ctor_get(v_impl_3611_, 3);
                        lean_inc(v_l_3698_);
                        if lean_obj_tag(v_l_3698_) == 0 {
                            v_r_3699_ = lean_ctor_get(v_impl_3611_, 4);
                            v_k_3700_ = lean_ctor_get(v_impl_3611_, 1);
                            v_v_3701_ = lean_ctor_get(v_impl_3611_, 2);
                            v_isSharedCheck_3712_ = (!lean_is_exclusive(v_impl_3611_)) as u8;
                            if v_isSharedCheck_3712_ == 0 {
                                v_unused_3713_ = lean_ctor_get(v_impl_3611_, 3);
                                lean_dec(v_unused_3713_);
                                v_unused_3714_ = lean_ctor_get(v_impl_3611_, 0);
                                lean_dec(v_unused_3714_);
                                v___x_3703_ = v_impl_3611_;
                                v_isShared_3704_ = v_isSharedCheck_3712_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_3699_);
                                lean_inc(v_v_3701_);
                                lean_inc(v_k_3700_);
                                lean_dec(v_impl_3611_);
                                v___x_3703_ = lean_box(0);
                                v_isShared_3704_ = v_isSharedCheck_3712_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_3715_ = lean_ctor_get(v_impl_3611_, 4);
                            lean_inc(v_r_3715_);
                            if lean_obj_tag(v_r_3715_) == 0 {
                                v_k_3716_ = lean_ctor_get(v_impl_3611_, 1);
                                v_v_3717_ = lean_ctor_get(v_impl_3611_, 2);
                                v_isSharedCheck_3740_ = (!lean_is_exclusive(v_impl_3611_)) as u8;
                                if v_isSharedCheck_3740_ == 0 {
                                    v_unused_3741_ = lean_ctor_get(v_impl_3611_, 4);
                                    lean_dec(v_unused_3741_);
                                    v_unused_3742_ = lean_ctor_get(v_impl_3611_, 3);
                                    lean_dec(v_unused_3742_);
                                    v_unused_3743_ = lean_ctor_get(v_impl_3611_, 0);
                                    lean_dec(v_unused_3743_);
                                    v___x_3719_ = v_impl_3611_;
                                    v_isShared_3720_ = v_isSharedCheck_3740_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_3717_);
                                    lean_inc(v_k_3716_);
                                    lean_dec(v_impl_3611_);
                                    v___x_3719_ = lean_box(0);
                                    v_isShared_3720_ = v_isSharedCheck_3740_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_3744_ = lean_unsigned_to_nat(2);
                                if v_isShared_3470_ == 0 {
                                    lean_ctor_set(v___x_3469_, 4, v_r_3715_);
                                    lean_ctor_set(v___x_3469_, 3, v_impl_3611_);
                                    lean_ctor_set(v___x_3469_, 0, v___x_3744_);
                                    v___x_3746_ = v___x_3469_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
                                    lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_k_3464_);
                                    lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_v_3465_);
                                    lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_impl_3611_);
                                    lean_ctor_set(v_reuseFailAlloc_3747_, 4, v_r_3715_);
                                    v___x_3746_ = v_reuseFailAlloc_3747_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3487_;
            }
            3 => {
                v_size_3492_ = lean_ctor_get(v_l_3479_, 0);
                v_k_3493_ = lean_ctor_get(v_l_3479_, 1);
                v_v_3494_ = lean_ctor_get(v_l_3479_, 2);
                v_l_3495_ = lean_ctor_get(v_l_3479_, 3);
                v_r_3496_ = lean_ctor_get(v_l_3479_, 4);
                v_size_3497_ = lean_ctor_get(v_r_3480_, 0);
                v___x_3498_ = lean_unsigned_to_nat(2);
                v___x_3499_ = lean_nat_mul(v___x_3498_, v_size_3497_);
                v___x_3500_ = lean_nat_dec_lt(v_size_3492_, v___x_3499_);
                lean_dec(v___x_3499_);
                if v___x_3500_ == 0 {
                    lean_inc(v_r_3496_);
                    lean_inc(v_l_3495_);
                    lean_inc(v_v_3494_);
                    lean_inc(v_k_3493_);
                    v_isSharedCheck_3528_ = (!lean_is_exclusive(v_l_3479_)) as u8;
                    if v_isSharedCheck_3528_ == 0 {
                        v_unused_3529_ = lean_ctor_get(v_l_3479_, 4);
                        lean_dec(v_unused_3529_);
                        v_unused_3530_ = lean_ctor_get(v_l_3479_, 3);
                        lean_dec(v_unused_3530_);
                        v_unused_3531_ = lean_ctor_get(v_l_3479_, 2);
                        lean_dec(v_unused_3531_);
                        v_unused_3532_ = lean_ctor_get(v_l_3479_, 1);
                        lean_dec(v_unused_3532_);
                        v_unused_3533_ = lean_ctor_get(v_l_3479_, 0);
                        lean_dec(v_unused_3533_);
                        v___x_3502_ = v_l_3479_;
                        v_isShared_3503_ = v_isSharedCheck_3528_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_3479_);
                        v___x_3502_ = lean_box(0);
                        v_isShared_3503_ = v_isSharedCheck_3528_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3469_);
                    v___x_3534_ = lean_nat_add(v___x_3474_, v_size_3475_);
                    v___x_3535_ = lean_nat_add(v___x_3534_, v_size_3476_);
                    lean_dec(v_size_3476_);
                    v___x_3536_ = lean_nat_add(v___x_3534_, v_size_3492_);
                    lean_dec(v___x_3534_);
                    lean_inc_ref(v_l_3466_);
                    if v_isShared_3491_ == 0 {
                        lean_ctor_set(v___x_3490_, 4, v_l_3479_);
                        lean_ctor_set(v___x_3490_, 3, v_l_3466_);
                        lean_ctor_set(v___x_3490_, 2, v_v_3465_);
                        lean_ctor_set(v___x_3490_, 1, v_k_3464_);
                        lean_ctor_set(v___x_3490_, 0, v___x_3536_);
                        v___x_3538_ = v___x_3490_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3536_);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_k_3464_);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 2, v_v_3465_);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 3, v_l_3466_);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 4, v_l_3479_);
                        v___x_3538_ = v_reuseFailAlloc_3551_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3504_ = lean_nat_add(v___x_3474_, v_size_3475_);
                v___x_3505_ = lean_nat_add(v___x_3504_, v_size_3476_);
                lean_dec(v_size_3476_);
                if lean_obj_tag(v_l_3495_) == 0 {
                    v_size_3526_ = lean_ctor_get(v_l_3495_, 0);
                    lean_inc(v_size_3526_);
                    v___y_3518_ = v_size_3526_;
                    state = 8;
                    continue;
                } else {
                    v___x_3527_ = lean_unsigned_to_nat(0);
                    v___y_3518_ = v___x_3527_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3510_ = lean_nat_add(v___y_3507_, v___y_3509_);
                lean_dec(v___y_3509_);
                lean_dec(v___y_3507_);
                if v_isShared_3503_ == 0 {
                    lean_ctor_set(v___x_3502_, 4, v_r_3480_);
                    lean_ctor_set(v___x_3502_, 3, v_r_3496_);
                    lean_ctor_set(v___x_3502_, 2, v_v_3478_);
                    lean_ctor_set(v___x_3502_, 1, v_k_3477_);
                    lean_ctor_set(v___x_3502_, 0, v___x_3510_);
                    v___x_3512_ = v___x_3502_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3510_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_k_3477_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_v_3478_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 3, v_r_3496_);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 4, v_r_3480_);
                    v___x_3512_ = v_reuseFailAlloc_3516_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3491_ == 0 {
                    lean_ctor_set(v___x_3490_, 4, v___x_3512_);
                    lean_ctor_set(v___x_3490_, 3, v___y_3508_);
                    lean_ctor_set(v___x_3490_, 2, v_v_3494_);
                    lean_ctor_set(v___x_3490_, 1, v_k_3493_);
                    lean_ctor_set(v___x_3490_, 0, v___x_3505_);
                    v___x_3514_ = v___x_3490_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3505_);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3493_);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3494_);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 3, v___y_3508_);
                    lean_ctor_set(v_reuseFailAlloc_3515_, 4, v___x_3512_);
                    v___x_3514_ = v_reuseFailAlloc_3515_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3514_;
            }
            8 => {
                v___x_3519_ = lean_nat_add(v___x_3504_, v___y_3518_);
                lean_dec(v___y_3518_);
                lean_dec(v___x_3504_);
                if v_isShared_3470_ == 0 {
                    lean_ctor_set(v___x_3469_, 4, v_l_3495_);
                    lean_ctor_set(v___x_3469_, 0, v___x_3519_);
                    v___x_3521_ = v___x_3469_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3519_);
                    lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_k_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_v_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_l_3466_);
                    lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_l_3495_);
                    v___x_3521_ = v_reuseFailAlloc_3525_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3522_ = lean_nat_add(v___x_3474_, v_size_3497_);
                if lean_obj_tag(v_r_3496_) == 0 {
                    v_size_3523_ = lean_ctor_get(v_r_3496_, 0);
                    lean_inc(v_size_3523_);
                    v___y_3507_ = v___x_3522_;
                    v___y_3508_ = v___x_3521_;
                    v___y_3509_ = v_size_3523_;
                    state = 5;
                    continue;
                } else {
                    v___x_3524_ = lean_unsigned_to_nat(0);
                    v___y_3507_ = v___x_3522_;
                    v___y_3508_ = v___x_3521_;
                    v___y_3509_ = v___x_3524_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3545_ = (!lean_is_exclusive(v_l_3466_)) as u8;
                if v_isSharedCheck_3545_ == 0 {
                    v_unused_3546_ = lean_ctor_get(v_l_3466_, 4);
                    lean_dec(v_unused_3546_);
                    v_unused_3547_ = lean_ctor_get(v_l_3466_, 3);
                    lean_dec(v_unused_3547_);
                    v_unused_3548_ = lean_ctor_get(v_l_3466_, 2);
                    lean_dec(v_unused_3548_);
                    v_unused_3549_ = lean_ctor_get(v_l_3466_, 1);
                    lean_dec(v_unused_3549_);
                    v_unused_3550_ = lean_ctor_get(v_l_3466_, 0);
                    lean_dec(v_unused_3550_);
                    v___x_3540_ = v_l_3466_;
                    v_isShared_3541_ = v_isSharedCheck_3545_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_3466_);
                    v___x_3540_ = lean_box(0);
                    v_isShared_3541_ = v_isSharedCheck_3545_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3541_ == 0 {
                    lean_ctor_set(v___x_3540_, 4, v_r_3480_);
                    lean_ctor_set(v___x_3540_, 3, v___x_3538_);
                    lean_ctor_set(v___x_3540_, 2, v_v_3478_);
                    lean_ctor_set(v___x_3540_, 1, v_k_3477_);
                    lean_ctor_set(v___x_3540_, 0, v___x_3535_);
                    v___x_3543_ = v___x_3540_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3535_);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_k_3477_);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_v_3478_);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 3, v___x_3538_);
                    lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_r_3480_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3543_;
            }
            13 => {
                v_k_3565_ = lean_ctor_get(v_l_3558_, 1);
                v_v_3566_ = lean_ctor_get(v_l_3558_, 2);
                v_isSharedCheck_3580_ = (!lean_is_exclusive(v_l_3558_)) as u8;
                if v_isSharedCheck_3580_ == 0 {
                    v_unused_3581_ = lean_ctor_get(v_l_3558_, 4);
                    lean_dec(v_unused_3581_);
                    v_unused_3582_ = lean_ctor_get(v_l_3558_, 3);
                    lean_dec(v_unused_3582_);
                    v_unused_3583_ = lean_ctor_get(v_l_3558_, 0);
                    lean_dec(v_unused_3583_);
                    v___x_3568_ = v_l_3558_;
                    v_isShared_3569_ = v_isSharedCheck_3580_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_3566_);
                    lean_inc(v_k_3565_);
                    lean_dec(v_l_3558_);
                    v___x_3568_ = lean_box(0);
                    v_isShared_3569_ = v_isSharedCheck_3580_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3570_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3559_, 2);
                if v_isShared_3569_ == 0 {
                    lean_ctor_set(v___x_3568_, 4, v_r_3559_);
                    lean_ctor_set(v___x_3568_, 3, v_r_3559_);
                    lean_ctor_set(v___x_3568_, 2, v_v_3465_);
                    lean_ctor_set(v___x_3568_, 1, v_k_3464_);
                    lean_ctor_set(v___x_3568_, 0, v___x_3474_);
                    v___x_3572_ = v___x_3568_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3474_);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_k_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_v_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_r_3559_);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_r_3559_);
                    v___x_3572_ = v_reuseFailAlloc_3579_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_3559_);
                if v_isShared_3564_ == 0 {
                    lean_ctor_set(v___x_3563_, 3, v_r_3559_);
                    lean_ctor_set(v___x_3563_, 0, v___x_3474_);
                    v___x_3574_ = v___x_3563_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3474_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_k_3560_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_v_3561_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_r_3559_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_r_3559_);
                    v___x_3574_ = v_reuseFailAlloc_3578_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3470_ == 0 {
                    lean_ctor_set(v___x_3469_, 4, v___x_3574_);
                    lean_ctor_set(v___x_3469_, 3, v___x_3572_);
                    lean_ctor_set(v___x_3469_, 2, v_v_3566_);
                    lean_ctor_set(v___x_3469_, 1, v_k_3565_);
                    lean_ctor_set(v___x_3469_, 0, v___x_3570_);
                    v___x_3576_ = v___x_3469_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3570_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_k_3565_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_v_3566_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 3, v___x_3572_);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 4, v___x_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3577_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3576_;
            }
            18 => {
                v___x_3593_ = lean_unsigned_to_nat(3);
                if v_isShared_3592_ == 0 {
                    lean_ctor_set(v___x_3591_, 4, v_l_3558_);
                    lean_ctor_set(v___x_3591_, 2, v_v_3465_);
                    lean_ctor_set(v___x_3591_, 1, v_k_3464_);
                    lean_ctor_set(v___x_3591_, 0, v___x_3474_);
                    v___x_3595_ = v___x_3591_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3474_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_k_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_v_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 3, v_l_3558_);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 4, v_l_3558_);
                    v___x_3595_ = v_reuseFailAlloc_3599_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3470_ == 0 {
                    lean_ctor_set(v___x_3469_, 4, v_r_3587_);
                    lean_ctor_set(v___x_3469_, 3, v___x_3595_);
                    lean_ctor_set(v___x_3469_, 2, v_v_3589_);
                    lean_ctor_set(v___x_3469_, 1, v_k_3588_);
                    lean_ctor_set(v___x_3469_, 0, v___x_3593_);
                    v___x_3597_ = v___x_3469_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3593_);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_k_3588_);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_v_3589_);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 3, v___x_3595_);
                    lean_ctor_set(v_reuseFailAlloc_3598_, 4, v_r_3587_);
                    v___x_3597_ = v_reuseFailAlloc_3598_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3597_;
            }
            21 => {
                return v___x_3606_;
            }
            22 => {
                return v___x_3609_;
            }
            23 => {
                return v___x_3625_;
            }
            24 => {
                v_size_3630_ = lean_ctor_get(v_l_3617_, 0);
                v_size_3631_ = lean_ctor_get(v_r_3618_, 0);
                v_k_3632_ = lean_ctor_get(v_r_3618_, 1);
                v_v_3633_ = lean_ctor_get(v_r_3618_, 2);
                v_l_3634_ = lean_ctor_get(v_r_3618_, 3);
                v_r_3635_ = lean_ctor_get(v_r_3618_, 4);
                v___x_3636_ = lean_unsigned_to_nat(2);
                v___x_3637_ = lean_nat_mul(v___x_3636_, v_size_3630_);
                v___x_3638_ = lean_nat_dec_lt(v_size_3631_, v___x_3637_);
                lean_dec(v___x_3637_);
                if v___x_3638_ == 0 {
                    lean_inc(v_r_3635_);
                    lean_inc(v_l_3634_);
                    lean_inc(v_v_3633_);
                    lean_inc(v_k_3632_);
                    v_isSharedCheck_3667_ = (!lean_is_exclusive(v_r_3618_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v_unused_3668_ = lean_ctor_get(v_r_3618_, 4);
                        lean_dec(v_unused_3668_);
                        v_unused_3669_ = lean_ctor_get(v_r_3618_, 3);
                        lean_dec(v_unused_3669_);
                        v_unused_3670_ = lean_ctor_get(v_r_3618_, 2);
                        lean_dec(v_unused_3670_);
                        v_unused_3671_ = lean_ctor_get(v_r_3618_, 1);
                        lean_dec(v_unused_3671_);
                        v_unused_3672_ = lean_ctor_get(v_r_3618_, 0);
                        lean_dec(v_unused_3672_);
                        v___x_3640_ = v_r_3618_;
                        v_isShared_3641_ = v_isSharedCheck_3667_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_3618_);
                        v___x_3640_ = lean_box(0);
                        v_isShared_3641_ = v_isSharedCheck_3667_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3469_);
                    v___x_3673_ = lean_nat_add(v___x_3612_, v_size_3614_);
                    lean_dec(v_size_3614_);
                    v___x_3674_ = lean_nat_add(v___x_3673_, v_size_3613_);
                    lean_dec(v___x_3673_);
                    v___x_3675_ = lean_nat_add(v___x_3612_, v_size_3613_);
                    v___x_3676_ = lean_nat_add(v___x_3675_, v_size_3631_);
                    lean_dec(v___x_3675_);
                    lean_inc_ref(v_r_3467_);
                    if v_isShared_3629_ == 0 {
                        lean_ctor_set(v___x_3628_, 4, v_r_3467_);
                        lean_ctor_set(v___x_3628_, 3, v_r_3618_);
                        lean_ctor_set(v___x_3628_, 2, v_v_3465_);
                        lean_ctor_set(v___x_3628_, 1, v_k_3464_);
                        lean_ctor_set(v___x_3628_, 0, v___x_3676_);
                        v___x_3678_ = v___x_3628_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3676_);
                        lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_k_3464_);
                        lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_v_3465_);
                        lean_ctor_set(v_reuseFailAlloc_3691_, 3, v_r_3618_);
                        lean_ctor_set(v_reuseFailAlloc_3691_, 4, v_r_3467_);
                        v___x_3678_ = v_reuseFailAlloc_3691_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3642_ = lean_nat_add(v___x_3612_, v_size_3614_);
                lean_dec(v_size_3614_);
                v___x_3643_ = lean_nat_add(v___x_3642_, v_size_3613_);
                lean_dec(v___x_3642_);
                v___x_3655_ = lean_nat_add(v___x_3612_, v_size_3630_);
                if lean_obj_tag(v_l_3634_) == 0 {
                    v_size_3665_ = lean_ctor_get(v_l_3634_, 0);
                    lean_inc(v_size_3665_);
                    v___y_3657_ = v_size_3665_;
                    state = 29;
                    continue;
                } else {
                    v___x_3666_ = lean_unsigned_to_nat(0);
                    v___y_3657_ = v___x_3666_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3648_ = lean_nat_add(v___y_3646_, v___y_3647_);
                lean_dec(v___y_3647_);
                lean_dec(v___y_3646_);
                if v_isShared_3641_ == 0 {
                    lean_ctor_set(v___x_3640_, 4, v_r_3467_);
                    lean_ctor_set(v___x_3640_, 3, v_r_3635_);
                    lean_ctor_set(v___x_3640_, 2, v_v_3465_);
                    lean_ctor_set(v___x_3640_, 1, v_k_3464_);
                    lean_ctor_set(v___x_3640_, 0, v___x_3648_);
                    v___x_3650_ = v___x_3640_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3648_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_k_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_v_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 3, v_r_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 4, v_r_3467_);
                    v___x_3650_ = v_reuseFailAlloc_3654_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3629_ == 0 {
                    lean_ctor_set(v___x_3628_, 4, v___x_3650_);
                    lean_ctor_set(v___x_3628_, 3, v___y_3645_);
                    lean_ctor_set(v___x_3628_, 2, v_v_3633_);
                    lean_ctor_set(v___x_3628_, 1, v_k_3632_);
                    lean_ctor_set(v___x_3628_, 0, v___x_3643_);
                    v___x_3652_ = v___x_3628_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3643_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_k_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_v_3633_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 3, v___y_3645_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 4, v___x_3650_);
                    v___x_3652_ = v_reuseFailAlloc_3653_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3652_;
            }
            29 => {
                v___x_3658_ = lean_nat_add(v___x_3655_, v___y_3657_);
                lean_dec(v___y_3657_);
                lean_dec(v___x_3655_);
                if v_isShared_3470_ == 0 {
                    lean_ctor_set(v___x_3469_, 4, v_l_3634_);
                    lean_ctor_set(v___x_3469_, 3, v_l_3617_);
                    lean_ctor_set(v___x_3469_, 2, v_v_3616_);
                    lean_ctor_set(v___x_3469_, 1, v_k_3615_);
                    lean_ctor_set(v___x_3469_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3469_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3658_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_k_3615_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_v_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_l_3617_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 4, v_l_3634_);
                    v___x_3660_ = v_reuseFailAlloc_3664_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3661_ = lean_nat_add(v___x_3612_, v_size_3613_);
                if lean_obj_tag(v_r_3635_) == 0 {
                    v_size_3662_ = lean_ctor_get(v_r_3635_, 0);
                    lean_inc(v_size_3662_);
                    v___y_3645_ = v___x_3660_;
                    v___y_3646_ = v___x_3661_;
                    v___y_3647_ = v_size_3662_;
                    state = 26;
                    continue;
                } else {
                    v___x_3663_ = lean_unsigned_to_nat(0);
                    v___y_3645_ = v___x_3660_;
                    v___y_3646_ = v___x_3661_;
                    v___y_3647_ = v___x_3663_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3685_ = (!lean_is_exclusive(v_r_3467_)) as u8;
                if v_isSharedCheck_3685_ == 0 {
                    v_unused_3686_ = lean_ctor_get(v_r_3467_, 4);
                    lean_dec(v_unused_3686_);
                    v_unused_3687_ = lean_ctor_get(v_r_3467_, 3);
                    lean_dec(v_unused_3687_);
                    v_unused_3688_ = lean_ctor_get(v_r_3467_, 2);
                    lean_dec(v_unused_3688_);
                    v_unused_3689_ = lean_ctor_get(v_r_3467_, 1);
                    lean_dec(v_unused_3689_);
                    v_unused_3690_ = lean_ctor_get(v_r_3467_, 0);
                    lean_dec(v_unused_3690_);
                    v___x_3680_ = v_r_3467_;
                    v_isShared_3681_ = v_isSharedCheck_3685_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_3467_);
                    v___x_3680_ = lean_box(0);
                    v_isShared_3681_ = v_isSharedCheck_3685_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3681_ == 0 {
                    lean_ctor_set(v___x_3680_, 4, v___x_3678_);
                    lean_ctor_set(v___x_3680_, 3, v_l_3617_);
                    lean_ctor_set(v___x_3680_, 2, v_v_3616_);
                    lean_ctor_set(v___x_3680_, 1, v_k_3615_);
                    lean_ctor_set(v___x_3680_, 0, v___x_3674_);
                    v___x_3683_ = v___x_3680_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3674_);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_k_3615_);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_v_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_l_3617_);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 4, v___x_3678_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3683_;
            }
            34 => {
                v___x_3705_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_3699_);
                if v_isShared_3704_ == 0 {
                    lean_ctor_set(v___x_3703_, 3, v_r_3699_);
                    lean_ctor_set(v___x_3703_, 2, v_v_3465_);
                    lean_ctor_set(v___x_3703_, 1, v_k_3464_);
                    lean_ctor_set(v___x_3703_, 0, v___x_3612_);
                    v___x_3707_ = v___x_3703_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_k_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 2, v_v_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 3, v_r_3699_);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 4, v_r_3699_);
                    v___x_3707_ = v_reuseFailAlloc_3711_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3470_ == 0 {
                    lean_ctor_set(v___x_3469_, 4, v___x_3707_);
                    lean_ctor_set(v___x_3469_, 3, v_l_3698_);
                    lean_ctor_set(v___x_3469_, 2, v_v_3701_);
                    lean_ctor_set(v___x_3469_, 1, v_k_3700_);
                    lean_ctor_set(v___x_3469_, 0, v___x_3705_);
                    v___x_3709_ = v___x_3469_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3705_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_k_3700_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_v_3701_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_l_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 4, v___x_3707_);
                    v___x_3709_ = v_reuseFailAlloc_3710_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3709_;
            }
            37 => {
                v_k_3721_ = lean_ctor_get(v_r_3715_, 1);
                v_v_3722_ = lean_ctor_get(v_r_3715_, 2);
                v_isSharedCheck_3736_ = (!lean_is_exclusive(v_r_3715_)) as u8;
                if v_isSharedCheck_3736_ == 0 {
                    v_unused_3737_ = lean_ctor_get(v_r_3715_, 4);
                    lean_dec(v_unused_3737_);
                    v_unused_3738_ = lean_ctor_get(v_r_3715_, 3);
                    lean_dec(v_unused_3738_);
                    v_unused_3739_ = lean_ctor_get(v_r_3715_, 0);
                    lean_dec(v_unused_3739_);
                    v___x_3724_ = v_r_3715_;
                    v_isShared_3725_ = v_isSharedCheck_3736_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_3722_);
                    lean_inc(v_k_3721_);
                    lean_dec(v_r_3715_);
                    v___x_3724_ = lean_box(0);
                    v_isShared_3725_ = v_isSharedCheck_3736_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3726_ = lean_unsigned_to_nat(3);
                if v_isShared_3725_ == 0 {
                    lean_ctor_set(v___x_3724_, 4, v_l_3698_);
                    lean_ctor_set(v___x_3724_, 3, v_l_3698_);
                    lean_ctor_set(v___x_3724_, 2, v_v_3717_);
                    lean_ctor_set(v___x_3724_, 1, v_k_3716_);
                    lean_ctor_set(v___x_3724_, 0, v___x_3612_);
                    v___x_3728_ = v___x_3724_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_k_3716_);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 2, v_v_3717_);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 3, v_l_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 4, v_l_3698_);
                    v___x_3728_ = v_reuseFailAlloc_3735_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3720_ == 0 {
                    lean_ctor_set(v___x_3719_, 4, v_l_3698_);
                    lean_ctor_set(v___x_3719_, 2, v_v_3465_);
                    lean_ctor_set(v___x_3719_, 1, v_k_3464_);
                    lean_ctor_set(v___x_3719_, 0, v___x_3612_);
                    v___x_3730_ = v___x_3719_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_k_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_v_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_l_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_l_3698_);
                    v___x_3730_ = v_reuseFailAlloc_3734_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3470_ == 0 {
                    lean_ctor_set(v___x_3469_, 4, v___x_3730_);
                    lean_ctor_set(v___x_3469_, 3, v___x_3728_);
                    lean_ctor_set(v___x_3469_, 2, v_v_3722_);
                    lean_ctor_set(v___x_3469_, 1, v_k_3721_);
                    lean_ctor_set(v___x_3469_, 0, v___x_3726_);
                    v___x_3732_ = v___x_3469_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3726_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3721_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3722_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 3, v___x_3728_);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 4, v___x_3730_);
                    v___x_3732_ = v_reuseFailAlloc_3733_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3732_;
            }
            42 => {
                return v___x_3746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(
    mut v_a_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v_self_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_x3f_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v_a_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3792_: u8 = 0;
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3758_ = lean_st_ref_get(v___y_3752_);
                v_fst_3759_ = lean_ctor_get(v_a_3751_, 0);
                v_snd_3760_ = lean_ctor_get(v_a_3751_, 1);
                v_isSharedCheck_3793_ = (!lean_is_exclusive(v_a_3751_)) as u8;
                if v_isSharedCheck_3793_ == 0 {
                    v___x_3762_ = v_a_3751_;
                    v_isShared_3763_ = v_isSharedCheck_3793_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3760_);
                    lean_inc(v_fst_3759_);
                    lean_dec(v_a_3751_);
                    v___x_3762_ = lean_box(0);
                    v_isShared_3763_ = v_isSharedCheck_3793_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_3760_);
                v___x_3764_ = l_Lean_Meta_Grind_Goal_getENode(
                    v___x_3758_,
                    v_snd_3760_,
                    v___y_3753_,
                    v___y_3754_,
                    v___y_3755_,
                    v___y_3756_,
                );
                lean_dec(v___x_3758_);
                if lean_obj_tag(v___x_3764_) == 0 {
                    v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3784_ = (!lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3784_ == 0 {
                        v___x_3767_ = v___x_3764_;
                        v_isShared_3768_ = v_isSharedCheck_3784_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3765_);
                        lean_dec(v___x_3764_);
                        v___x_3767_ = lean_box(0);
                        v_isShared_3768_ = v_isSharedCheck_3784_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3762_);
                    lean_dec(v_snd_3760_);
                    lean_dec(v_fst_3759_);
                    v_a_3785_ = lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3792_ = (!lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3792_ == 0 {
                        v___x_3787_ = v___x_3764_;
                        v_isShared_3788_ = v_isSharedCheck_3792_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3785_);
                        lean_dec(v___x_3764_);
                        v___x_3787_ = lean_box(0);
                        v_isShared_3788_ = v_isSharedCheck_3792_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_self_3769_ = lean_ctor_get(v_a_3765_, 0);
                lean_inc_ref(v_self_3769_);
                v_target_x3f_3770_ = lean_ctor_get(v_a_3765_, 4);
                lean_inc(v_target_x3f_3770_);
                v_idx_3771_ = lean_ctor_get(v_a_3765_, 7);
                lean_inc(v_idx_3771_);
                lean_dec(v_a_3765_);
                v___x_3772_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_idx_3771_, v_self_3769_, v_fst_3759_);
                if lean_obj_tag(v_target_x3f_3770_) == 1 {
                    lean_del_object(v___x_3767_);
                    lean_dec(v_snd_3760_);
                    v_val_3773_ = lean_ctor_get(v_target_x3f_3770_, 0);
                    lean_inc(v_val_3773_);
                    lean_dec_ref_known(v_target_x3f_3770_, 1);
                    if v_isShared_3763_ == 0 {
                        lean_ctor_set(v___x_3762_, 1, v_val_3773_);
                        lean_ctor_set(v___x_3762_, 0, v___x_3772_);
                        v___x_3775_ = v___x_3762_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3772_);
                        lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_val_3773_);
                        v___x_3775_ = v_reuseFailAlloc_3777_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_target_x3f_3770_);
                    if v_isShared_3763_ == 0 {
                        lean_ctor_set(v___x_3762_, 0, v___x_3772_);
                        v___x_3779_ = v___x_3762_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3772_);
                        lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_snd_3760_);
                        v___x_3779_ = v_reuseFailAlloc_3783_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_3751_ = v___x_3775_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3768_ == 0 {
                    lean_ctor_set(v___x_3767_, 0, v___x_3779_);
                    v___x_3781_ = v___x_3767_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3781_;
            }
            6 => {
                if v_isShared_3788_ == 0 {
                    v___x_3790_ = v___x_3787_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
                    v___x_3790_ = v_reuseFailAlloc_3791_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg___boxed(
    mut v_a_3794_: *mut LeanObject,
    mut v___y_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
    mut v___y_3800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3801_: *mut LeanObject = core::ptr::null_mut();
    v_res_3801_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
    lean_dec(v___y_3799_);
    lean_dec_ref(v___y_3798_);
    lean_dec(v___y_3797_);
    lean_dec_ref(v___y_3796_);
    lean_dec(v___y_3795_);
    return v_res_3801_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0()
-> *mut LeanObject {
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    v___x_3802_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_3803_ = lean_unsigned_to_nat(2);
    v___x_3804_ = lean_unsigned_to_nat(89);
    v___x_3805_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__1;
    v___x_3806_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_3807_ = l_mkPanicMessageWithDecl(
        v___x_3806_,
        v___x_3805_,
        v___x_3804_,
        v___x_3803_,
        v___x_3802_,
    );
    return v___x_3807_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(
    mut v_lhs_3808_: *mut LeanObject,
    mut v_rhs_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
    mut v_a_3811_: *mut LeanObject,
    mut v_a_3812_: *mut LeanObject,
    mut v_a_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_visited_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v_fst_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v_a_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_reuseFailAlloc_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v_unused_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_3821_ = lean_box(1);
                v___x_3822_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3822_, 0, v_visited_3821_);
                lean_ctor_set(v___x_3822_, 1, v_lhs_3808_);
                v___x_3823_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v___x_3822_, v_a_3810_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
                if lean_obj_tag(v___x_3823_) == 0 {
                    v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
                    lean_inc(v_a_3824_);
                    lean_dec_ref_known(v___x_3823_, 1);
                    v_fst_3825_ = lean_ctor_get(v_a_3824_, 0);
                    v_isSharedCheck_3854_ = (!lean_is_exclusive(v_a_3824_)) as u8;
                    if v_isSharedCheck_3854_ == 0 {
                        v_unused_3855_ = lean_ctor_get(v_a_3824_, 1);
                        lean_dec(v_unused_3855_);
                        v___x_3827_ = v_a_3824_;
                        v_isShared_3828_ = v_isSharedCheck_3854_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_3825_);
                        lean_dec(v_a_3824_);
                        v___x_3827_ = lean_box(0);
                        v_isShared_3828_ = v_isSharedCheck_3854_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_rhs_3809_);
                    v_a_3856_ = lean_ctor_get(v___x_3823_, 0);
                    v_isSharedCheck_3863_ = (!lean_is_exclusive(v___x_3823_)) as u8;
                    if v_isSharedCheck_3863_ == 0 {
                        v___x_3858_ = v___x_3823_;
                        v_isShared_3859_ = v_isSharedCheck_3863_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3856_);
                        lean_dec(v___x_3823_);
                        v___x_3858_ = lean_box(0);
                        v_isShared_3859_ = v_isSharedCheck_3863_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3829_ = lean_box(0);
                if v_isShared_3828_ == 0 {
                    lean_ctor_set(v___x_3827_, 1, v_rhs_3809_);
                    lean_ctor_set(v___x_3827_, 0, v___x_3829_);
                    v___x_3831_ = v___x_3827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3829_);
                    lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_rhs_3809_);
                    v___x_3831_ = v_reuseFailAlloc_3853_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3832_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v_fst_3825_, v___x_3831_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
                lean_dec(v_fst_3825_);
                if lean_obj_tag(v___x_3832_) == 0 {
                    v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
                    v_isSharedCheck_3844_ = (!lean_is_exclusive(v___x_3832_)) as u8;
                    if v_isSharedCheck_3844_ == 0 {
                        v___x_3835_ = v___x_3832_;
                        v_isShared_3836_ = v_isSharedCheck_3844_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3833_);
                        lean_dec(v___x_3832_);
                        v___x_3835_ = lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3844_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3845_ = lean_ctor_get(v___x_3832_, 0);
                    v_isSharedCheck_3852_ = (!lean_is_exclusive(v___x_3832_)) as u8;
                    if v_isSharedCheck_3852_ == 0 {
                        v___x_3847_ = v___x_3832_;
                        v_isShared_3848_ = v_isSharedCheck_3852_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3845_);
                        lean_dec(v___x_3832_);
                        v___x_3847_ = lean_box(0);
                        v_isShared_3848_ = v_isSharedCheck_3852_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_3837_ = lean_ctor_get(v_a_3833_, 0);
                lean_inc(v_fst_3837_);
                lean_dec(v_a_3833_);
                if lean_obj_tag(v_fst_3837_) == 0 {
                    lean_del_object(v___x_3835_);
                    v___x_3838_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___closed__0);
                    v___x_3839_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_3838_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
                    return v___x_3839_;
                } else {
                    v_val_3840_ = lean_ctor_get(v_fst_3837_, 0);
                    lean_inc(v_val_3840_);
                    lean_dec_ref_known(v_fst_3837_, 1);
                    if v_isShared_3836_ == 0 {
                        lean_ctor_set(v___x_3835_, 0, v_val_3840_);
                        v___x_3842_ = v___x_3835_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_val_3840_);
                        v___x_3842_ = v_reuseFailAlloc_3843_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3842_;
            }
            5 => {
                if v_isShared_3848_ == 0 {
                    v___x_3850_ = v___x_3847_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3850_;
            }
            7 => {
                if v_isShared_3859_ == 0 {
                    v___x_3861_ = v___x_3858_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
                    v___x_3861_ = v_reuseFailAlloc_3862_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon___boxed(
    mut v_lhs_3864_: *mut LeanObject,
    mut v_rhs_3865_: *mut LeanObject,
    mut v_a_3866_: *mut LeanObject,
    mut v_a_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
    mut v_a_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3877_: *mut LeanObject = core::ptr::null_mut();
    v_res_3877_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(
        v_lhs_3864_,
        v_rhs_3865_,
        v_a_3866_,
        v_a_3867_,
        v_a_3868_,
        v_a_3869_,
        v_a_3870_,
        v_a_3871_,
        v_a_3872_,
        v_a_3873_,
        v_a_3874_,
        v_a_3875_,
    );
    lean_dec(v_a_3875_);
    lean_dec_ref(v_a_3874_);
    lean_dec(v_a_3873_);
    lean_dec_ref(v_a_3872_);
    lean_dec(v_a_3871_);
    lean_dec_ref(v_a_3870_);
    lean_dec(v_a_3869_);
    lean_dec_ref(v_a_3868_);
    lean_dec(v_a_3867_);
    lean_dec(v_a_3866_);
    return v_res_3877_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0(
    mut v_00_u03b2_3878_: *mut LeanObject,
    mut v_k_3879_: *mut LeanObject,
    mut v_v_3880_: *mut LeanObject,
    mut v_t_3881_: *mut LeanObject,
    mut v_hl_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v___x_3883_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__0___redArg(v_k_3879_, v_v_3880_, v_t_3881_);
    return v___x_3883_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(
    mut v_inst_3884_: *mut LeanObject,
    mut v_a_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
    mut v___y_3889_: *mut LeanObject,
    mut v___y_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    v___x_3897_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___redArg(v_a_3885_, v___y_3886_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
    return v___x_3897_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1___boxed(
    mut v_inst_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v___y_3900_: *mut LeanObject,
    mut v___y_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
    mut v___y_3910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3911_: *mut LeanObject = core::ptr::null_mut();
    v_res_3911_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__1(v_inst_3898_, v_a_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
    lean_dec(v___y_3909_);
    lean_dec_ref(v___y_3908_);
    lean_dec(v___y_3907_);
    lean_dec_ref(v___y_3906_);
    lean_dec(v___y_3905_);
    lean_dec_ref(v___y_3904_);
    lean_dec(v___y_3903_);
    lean_dec_ref(v___y_3902_);
    lean_dec(v___y_3901_);
    lean_dec(v___y_3900_);
    return v_res_3911_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(
    mut v_00_u03b4_3912_: *mut LeanObject,
    mut v_t_3913_: *mut LeanObject,
    mut v_k_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___redArg(v_t_3913_, v_k_3914_);
    return v___x_3915_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2___boxed(
    mut v_00_u03b4_3916_: *mut LeanObject,
    mut v_t_3917_: *mut LeanObject,
    mut v_k_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3919_: *mut LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__2(v_00_u03b4_3916_, v_t_3917_, v_k_3918_);
    lean_dec(v_k_3918_);
    lean_dec(v_t_3917_);
    return v_res_3919_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(
    mut v___x_3920_: *mut LeanObject,
    mut v_inst_3921_: *mut LeanObject,
    mut v_a_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
    mut v___y_3925_: *mut LeanObject,
    mut v___y_3926_: *mut LeanObject,
    mut v___y_3927_: *mut LeanObject,
    mut v___y_3928_: *mut LeanObject,
    mut v___y_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v___y_3931_: *mut LeanObject,
    mut v___y_3932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v___x_3934_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg(v___x_3920_, v_a_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
    return v___x_3934_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___boxed(
    mut v___x_3935_: *mut LeanObject,
    mut v_inst_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
    mut v___y_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3949_: *mut LeanObject = core::ptr::null_mut();
    v_res_3949_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4(v___x_3935_, v_inst_3936_, v_a_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
    lean_dec(v___y_3947_);
    lean_dec_ref(v___y_3946_);
    lean_dec(v___y_3945_);
    lean_dec_ref(v___y_3944_);
    lean_dec(v___y_3943_);
    lean_dec_ref(v___y_3942_);
    lean_dec(v___y_3941_);
    lean_dec_ref(v___y_3940_);
    lean_dec(v___y_3939_);
    lean_dec(v___y_3938_);
    lean_dec(v___x_3935_);
    return v_res_3949_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(
    mut v_info_3950_: *mut LeanObject,
    mut v_lhs_3951_: *mut LeanObject,
    mut v_rhs_3952_: *mut LeanObject,
    mut v_i_3953_: *mut LeanObject,
    mut v_a_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
    mut v_a_3957_: *mut LeanObject,
    mut v_a_3958_: *mut LeanObject,
    mut v_a_3959_: *mut LeanObject,
    mut v_a_3960_: *mut LeanObject,
    mut v_a_3961_: *mut LeanObject,
    mut v_a_3962_: *mut LeanObject,
    mut v_a_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: u8 = 0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2081_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2082_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: u8 = 0;
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasFwdDeps_3993_: u8 = 0;
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3965_ = l_Lean_Expr_isApp(v_lhs_3951_);
                if v___x_3965_ == 0 {
                    lean_dec(v_i_3953_);
                    lean_dec_ref(v_rhs_3952_);
                    lean_dec_ref(v_lhs_3951_);
                    v___x_3966_ = 1;
                    v___x_3967_ = lean_box((v___x_3966_) as usize);
                    v___x_3968_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3968_, 0, v___x_3967_);
                    return v___x_3968_;
                } else {
                    v_a_u2081_3969_ = l_Lean_Expr_appArg_x21(v_lhs_3951_);
                    v_a_u2082_3970_ = l_Lean_Expr_appArg_x21(v_rhs_3952_);
                    v___x_3971_ = lean_unsigned_to_nat(1);
                    v_i_3972_ = lean_nat_sub(v_i_3953_, v___x_3971_);
                    lean_dec(v_i_3953_);
                    v___x_3987_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_u2081_3969_,
                            v_a_u2082_3970_,
                        );
                    lean_dec_ref(v_a_u2082_3970_);
                    lean_dec_ref(v_a_u2081_3969_);
                    if v___x_3987_ == 0 {
                        v___x_3988_ = lean_array_get_size(v_info_3950_);
                        v___x_3989_ = lean_nat_dec_lt(v_i_3972_, v___x_3988_);
                        if v___x_3989_ == 0 {
                            lean_dec(v_i_3972_);
                            lean_dec_ref(v_rhs_3952_);
                            lean_dec_ref(v_lhs_3951_);
                            v___x_3990_ = lean_box((v___x_3987_) as usize);
                            v___x_3991_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3991_, 0, v___x_3990_);
                            return v___x_3991_;
                        } else {
                            v___x_3992_ = lean_array_fget_borrowed(v_info_3950_, v_i_3972_);
                            v_hasFwdDeps_3993_ = lean_ctor_get_uint8(
                                v___x_3992_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            );
                            if v_hasFwdDeps_3993_ == 0 {
                                v___y_3974_ = v_a_3954_;
                                v___y_3975_ = v_a_3955_;
                                v___y_3976_ = v_a_3956_;
                                v___y_3977_ = v_a_3957_;
                                v___y_3978_ = v_a_3958_;
                                v___y_3979_ = v_a_3959_;
                                v___y_3980_ = v_a_3960_;
                                v___y_3981_ = v_a_3961_;
                                v___y_3982_ = v_a_3962_;
                                v___y_3983_ = v_a_3963_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_i_3972_);
                                lean_dec_ref(v_rhs_3952_);
                                lean_dec_ref(v_lhs_3951_);
                                v___x_3994_ = lean_box((v___x_3987_) as usize);
                                v___x_3995_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3995_, 0, v___x_3994_);
                                return v___x_3995_;
                            }
                        }
                    } else {
                        v___y_3974_ = v_a_3954_;
                        v___y_3975_ = v_a_3955_;
                        v___y_3976_ = v_a_3956_;
                        v___y_3977_ = v_a_3957_;
                        v___y_3978_ = v_a_3958_;
                        v___y_3979_ = v_a_3959_;
                        v___y_3980_ = v_a_3960_;
                        v___y_3981_ = v_a_3961_;
                        v___y_3982_ = v_a_3962_;
                        v___y_3983_ = v_a_3963_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3984_ = l_Lean_Expr_appFn_x21(v_lhs_3951_);
                lean_dec_ref(v_lhs_3951_);
                v___x_3985_ = l_Lean_Expr_appFn_x21(v_rhs_3952_);
                lean_dec_ref(v_rhs_3952_);
                v_lhs_3951_ = v___x_3984_;
                v_rhs_3952_ = v___x_3985_;
                v_i_3953_ = v_i_3972_;
                v_a_3954_ = v___y_3974_;
                v_a_3955_ = v___y_3975_;
                v_a_3956_ = v___y_3976_;
                v_a_3957_ = v___y_3977_;
                v_a_3958_ = v___y_3978_;
                v_a_3959_ = v___y_3979_;
                v_a_3960_ = v___y_3980_;
                v_a_3961_ = v___y_3981_;
                v_a_3962_ = v___y_3982_;
                v_a_3963_ = v___y_3983_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop___boxed(
    mut v_info_3996_: *mut LeanObject,
    mut v_lhs_3997_: *mut LeanObject,
    mut v_rhs_3998_: *mut LeanObject,
    mut v_i_3999_: *mut LeanObject,
    mut v_a_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
    mut v_a_4004_: *mut LeanObject,
    mut v_a_4005_: *mut LeanObject,
    mut v_a_4006_: *mut LeanObject,
    mut v_a_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
    mut v_a_4009_: *mut LeanObject,
    mut v_a_4010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4011_: *mut LeanObject = core::ptr::null_mut();
    v_res_4011_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(
            v_info_3996_,
            v_lhs_3997_,
            v_rhs_3998_,
            v_i_3999_,
            v_a_4000_,
            v_a_4001_,
            v_a_4002_,
            v_a_4003_,
            v_a_4004_,
            v_a_4005_,
            v_a_4006_,
            v_a_4007_,
            v_a_4008_,
            v_a_4009_,
        );
    lean_dec(v_a_4009_);
    lean_dec_ref(v_a_4008_);
    lean_dec(v_a_4007_);
    lean_dec_ref(v_a_4006_);
    lean_dec(v_a_4005_);
    lean_dec_ref(v_a_4004_);
    lean_dec(v_a_4003_);
    lean_dec_ref(v_a_4002_);
    lean_dec(v_a_4001_);
    lean_dec(v_a_4000_);
    lean_dec_ref(v_info_3996_);
    return v_res_4011_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(
    mut v_lhs_4012_: *mut LeanObject,
    mut v_rhs_4013_: *mut LeanObject,
    mut v_f_4014_: *mut LeanObject,
    mut v_g_4015_: *mut LeanObject,
    mut v_numArgs_4016_: *mut LeanObject,
    mut v_a_4017_: *mut LeanObject,
    mut v_a_4018_: *mut LeanObject,
    mut v_a_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
    mut v_a_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
    mut v_a_4024_: *mut LeanObject,
    mut v_a_4025_: *mut LeanObject,
    mut v_a_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4039_: u8 = 0;
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4028_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_f_4014_, v_g_4015_,
                    );
                if v___x_4028_ == 0 {
                    lean_dec(v_numArgs_4016_);
                    lean_dec_ref(v_f_4014_);
                    lean_dec_ref(v_rhs_4013_);
                    lean_dec_ref(v_lhs_4012_);
                    v___x_4029_ = lean_box((v___x_4028_) as usize);
                    v___x_4030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4030_, 0, v___x_4029_);
                    return v___x_4030_;
                } else {
                    v___x_4031_ = lean_box(0);
                    v___x_4032_ = l_Lean_Meta_getFunInfo(
                        v_f_4014_,
                        v___x_4031_,
                        v_a_4023_,
                        v_a_4024_,
                        v_a_4025_,
                        v_a_4026_,
                    );
                    if lean_obj_tag(v___x_4032_) == 0 {
                        v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
                        lean_inc(v_a_4033_);
                        lean_dec_ref_known(v___x_4032_, 1);
                        v_paramInfo_4034_ = lean_ctor_get(v_a_4033_, 0);
                        lean_inc_ref(v_paramInfo_4034_);
                        lean_dec(v_a_4033_);
                        v___x_4035_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget_loop(v_paramInfo_4034_, v_lhs_4012_, v_rhs_4013_, v_numArgs_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_);
                        lean_dec_ref(v_paramInfo_4034_);
                        return v___x_4035_;
                    } else {
                        lean_dec(v_numArgs_4016_);
                        lean_dec_ref(v_rhs_4013_);
                        lean_dec_ref(v_lhs_4012_);
                        v_a_4036_ = lean_ctor_get(v___x_4032_, 0);
                        v_isSharedCheck_4043_ = (!lean_is_exclusive(v___x_4032_)) as u8;
                        if v_isSharedCheck_4043_ == 0 {
                            v___x_4038_ = v___x_4032_;
                            v_isShared_4039_ = v_isSharedCheck_4043_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4036_);
                            lean_dec(v___x_4032_);
                            v___x_4038_ = lean_box(0);
                            v_isShared_4039_ = v_isSharedCheck_4043_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4039_ == 0 {
                    v___x_4041_ = v___x_4038_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
                    v___x_4041_ = v_reuseFailAlloc_4042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget___boxed(
    mut v_lhs_4044_: *mut LeanObject,
    mut v_rhs_4045_: *mut LeanObject,
    mut v_f_4046_: *mut LeanObject,
    mut v_g_4047_: *mut LeanObject,
    mut v_numArgs_4048_: *mut LeanObject,
    mut v_a_4049_: *mut LeanObject,
    mut v_a_4050_: *mut LeanObject,
    mut v_a_4051_: *mut LeanObject,
    mut v_a_4052_: *mut LeanObject,
    mut v_a_4053_: *mut LeanObject,
    mut v_a_4054_: *mut LeanObject,
    mut v_a_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
    mut v_a_4057_: *mut LeanObject,
    mut v_a_4058_: *mut LeanObject,
    mut v_a_4059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4060_: *mut LeanObject = core::ptr::null_mut();
    v_res_4060_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(
            v_lhs_4044_,
            v_rhs_4045_,
            v_f_4046_,
            v_g_4047_,
            v_numArgs_4048_,
            v_a_4049_,
            v_a_4050_,
            v_a_4051_,
            v_a_4052_,
            v_a_4053_,
            v_a_4054_,
            v_a_4055_,
            v_a_4056_,
            v_a_4057_,
            v_a_4058_,
        );
    lean_dec(v_a_4058_);
    lean_dec_ref(v_a_4057_);
    lean_dec(v_a_4056_);
    lean_dec_ref(v_a_4055_);
    lean_dec(v_a_4054_);
    lean_dec_ref(v_a_4053_);
    lean_dec(v_a_4052_);
    lean_dec_ref(v_a_4051_);
    lean_dec(v_a_4050_);
    lean_dec(v_a_4049_);
    lean_dec_ref(v_g_4047_);
    return v_res_4060_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    v___x_4061_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_4061_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(
    mut v_msg_4062_: *mut LeanObject,
    mut v___y_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
    mut v___y_4069_: *mut LeanObject,
    mut v___y_4070_: *mut LeanObject,
    mut v___y_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125372__overap_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    v___x_4074_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___closed__0);
    v___x_125372__overap_4075_ = lean_panic_fn_borrowed(v___x_4074_, v_msg_4062_);
    lean_inc(v___y_4072_);
    lean_inc_ref(v___y_4071_);
    lean_inc(v___y_4070_);
    lean_inc_ref(v___y_4069_);
    lean_inc(v___y_4068_);
    lean_inc_ref(v___y_4067_);
    lean_inc(v___y_4066_);
    lean_inc_ref(v___y_4065_);
    lean_inc(v___y_4064_);
    lean_inc(v___y_4063_);
    v___x_4076_ = lean_apply_11(
        v___x_125372__overap_4075_,
        v___y_4063_,
        v___y_4064_,
        v___y_4065_,
        v___y_4066_,
        v___y_4067_,
        v___y_4068_,
        v___y_4069_,
        v___y_4070_,
        v___y_4071_,
        v___y_4072_,
        lean_box(0),
    );
    return v___x_4076_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4___boxed(
    mut v_msg_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
    mut v___y_4086_: *mut LeanObject,
    mut v___y_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4089_: *mut LeanObject = core::ptr::null_mut();
    v_res_4089_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v_msg_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
    lean_dec(v___y_4087_);
    lean_dec_ref(v___y_4086_);
    lean_dec(v___y_4085_);
    lean_dec_ref(v___y_4084_);
    lean_dec(v___y_4083_);
    lean_dec_ref(v___y_4082_);
    lean_dec(v___y_4081_);
    lean_dec_ref(v___y_4080_);
    lean_dec(v___y_4079_);
    lean_dec(v___y_4078_);
    return v_res_4089_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4096_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4096_, 0, v___x_4095_);
    return v___x_4096_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    v___x_4097_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__3);
    v___x_4098_ = l_Lean_MessageData_ofFormat(v___x_4097_);
    return v___x_4098_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    v___x_4099_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__4);
    v___x_4100_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__2;
    v___x_4101_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_4101_, 0, v___x_4100_);
    lean_ctor_set(v___x_4101_, 1, v___x_4099_);
    return v___x_4101_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(
    mut v_ref_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    v___x_4104_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___closed__5);
    v___x_4105_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4105_, 0, v_ref_4102_);
    lean_ctor_set(v___x_4105_, 1, v___x_4104_);
    v___x_4106_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4106_, 0, v___x_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg___boxed(
    mut v_ref_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4109_: *mut LeanObject = core::ptr::null_mut();
    v_res_4109_ =
        l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(
            v_ref_4107_,
        );
    return v_res_4109_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(
    mut v_k_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
    mut v___y_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v_b_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4121_);
    lean_inc_ref(v___y_4120_);
    lean_inc(v___y_4119_);
    lean_inc_ref(v___y_4118_);
    lean_inc(v___y_4116_);
    lean_inc_ref(v___y_4115_);
    lean_inc(v___y_4114_);
    lean_inc_ref(v___y_4113_);
    lean_inc(v___y_4112_);
    lean_inc(v___y_4111_);
    v___x_4123_ = lean_apply_12(
        v_k_4110_,
        v_b_4117_,
        v___y_4111_,
        v___y_4112_,
        v___y_4113_,
        v___y_4114_,
        v___y_4115_,
        v___y_4116_,
        v___y_4118_,
        v___y_4119_,
        v___y_4120_,
        v___y_4121_,
        lean_box(0),
    );
    return v___x_4123_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed(
    mut v_k_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v_b_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4137_: *mut LeanObject = core::ptr::null_mut();
    v_res_4137_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0(v_k_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v_b_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
    lean_dec(v___y_4135_);
    lean_dec_ref(v___y_4134_);
    lean_dec(v___y_4133_);
    lean_dec_ref(v___y_4132_);
    lean_dec(v___y_4130_);
    lean_dec_ref(v___y_4129_);
    lean_dec(v___y_4128_);
    lean_dec_ref(v___y_4127_);
    lean_dec(v___y_4126_);
    lean_dec(v___y_4125_);
    return v_res_4137_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(
    mut v_name_4138_: *mut LeanObject,
    mut v_bi_4139_: u8,
    mut v_type_4140_: *mut LeanObject,
    mut v_k_4141_: *mut LeanObject,
    mut v_kind_4142_: u8,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4159_: u8 = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4148_);
                lean_inc_ref(v___y_4147_);
                lean_inc(v___y_4146_);
                lean_inc_ref(v___y_4145_);
                lean_inc(v___y_4144_);
                lean_inc(v___y_4143_);
                v___f_4154_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 7);
                lean_closure_set(v___f_4154_, 0, v_k_4141_);
                lean_closure_set(v___f_4154_, 1, v___y_4143_);
                lean_closure_set(v___f_4154_, 2, v___y_4144_);
                lean_closure_set(v___f_4154_, 3, v___y_4145_);
                lean_closure_set(v___f_4154_, 4, v___y_4146_);
                lean_closure_set(v___f_4154_, 5, v___y_4147_);
                lean_closure_set(v___f_4154_, 6, v___y_4148_);
                v___x_4155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_4138_,
                    v_bi_4139_,
                    v_type_4140_,
                    v___f_4154_,
                    v_kind_4142_,
                    v___y_4149_,
                    v___y_4150_,
                    v___y_4151_,
                    v___y_4152_,
                );
                if lean_obj_tag(v___x_4155_) == 0 {
                    return v___x_4155_;
                } else {
                    v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
                    v_isSharedCheck_4163_ = (!lean_is_exclusive(v___x_4155_)) as u8;
                    if v_isSharedCheck_4163_ == 0 {
                        v___x_4158_ = v___x_4155_;
                        v_isShared_4159_ = v_isSharedCheck_4163_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4156_);
                        lean_dec(v___x_4155_);
                        v___x_4158_ = lean_box(0);
                        v_isShared_4159_ = v_isSharedCheck_4163_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4159_ == 0 {
                    v___x_4161_ = v___x_4158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
                    v___x_4161_ = v_reuseFailAlloc_4162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg___boxed(
    mut v_name_4164_: *mut LeanObject,
    mut v_bi_4165_: *mut LeanObject,
    mut v_type_4166_: *mut LeanObject,
    mut v_k_4167_: *mut LeanObject,
    mut v_kind_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
    mut v___y_4173_: *mut LeanObject,
    mut v___y_4174_: *mut LeanObject,
    mut v___y_4175_: *mut LeanObject,
    mut v___y_4176_: *mut LeanObject,
    mut v___y_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4180_: u8 = 0;
    let mut v_kind_boxed_4181_: u8 = 0;
    let mut v_res_4182_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4180_ = (lean_unbox(v_bi_4165_) as u8);
    v_kind_boxed_4181_ = (lean_unbox(v_kind_4168_) as u8);
    v_res_4182_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_4164_, v_bi_boxed_4180_, v_type_4166_, v_k_4167_, v_kind_boxed_4181_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
    lean_dec(v___y_4178_);
    lean_dec_ref(v___y_4177_);
    lean_dec(v___y_4176_);
    lean_dec_ref(v___y_4175_);
    lean_dec(v___y_4174_);
    lean_dec_ref(v___y_4173_);
    lean_dec(v___y_4172_);
    lean_dec_ref(v___y_4171_);
    lean_dec(v___y_4170_);
    lean_dec(v___y_4169_);
    return v_res_4182_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(
    mut v_name_4183_: *mut LeanObject,
    mut v_type_4184_: *mut LeanObject,
    mut v_k_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4197_: u8 = 0;
    let mut v___x_4198_: u8 = 0;
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    v___x_4197_ = 0;
    v___x_4198_ = 0;
    v___x_4199_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_4183_, v___x_4197_, v_type_4184_, v_k_4185_, v___x_4198_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
    return v___x_4199_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg___boxed(
    mut v_name_4200_: *mut LeanObject,
    mut v_type_4201_: *mut LeanObject,
    mut v_k_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
    mut v___y_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
    mut v___y_4211_: *mut LeanObject,
    mut v___y_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4214_: *mut LeanObject = core::ptr::null_mut();
    v_res_4214_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_4200_, v_type_4201_, v_k_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
    lean_dec(v___y_4212_);
    lean_dec_ref(v___y_4211_);
    lean_dec(v___y_4210_);
    lean_dec_ref(v___y_4209_);
    lean_dec(v___y_4208_);
    lean_dec_ref(v___y_4207_);
    lean_dec(v___y_4206_);
    lean_dec_ref(v___y_4205_);
    lean_dec(v___y_4204_);
    lean_dec(v___y_4203_);
    return v_res_4214_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4216_: *mut LeanObject = core::ptr::null_mut();
    v___x_4215_ = lean_box(0);
    v_dummy_4216_ = l_Lean_Expr_sort___override(v___x_4215_);
    return v_dummy_4216_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(
    mut v_numArgs_4217_: *mut LeanObject,
    mut v_rhs_4218_: *mut LeanObject,
    mut v_lhs_4219_: *mut LeanObject,
    mut v___x_4220_: u8,
    mut v___x_4221_: u8,
    mut v_x_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
    mut v___y_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v_dummy_4234_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___closed__0);
    lean_inc(v_numArgs_4217_);
    v___x_4235_ = lean_mk_array(v_numArgs_4217_, v_dummy_4234_);
    v___x_4236_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(
        v_numArgs_4217_,
        v_rhs_4218_,
        v___x_4235_,
    );
    lean_inc_ref(v_x_4222_);
    v___x_4237_ = l_Lean_mkAppN(v_x_4222_, v___x_4236_);
    lean_dec_ref(v___x_4236_);
    v___x_4238_ = l_Lean_Meta_mkHEq(
        v_lhs_4219_,
        v___x_4237_,
        v___y_4229_,
        v___y_4230_,
        v___y_4231_,
        v___y_4232_,
    );
    if lean_obj_tag(v___x_4238_) == 0 {
        let mut v_a_4239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4243_: u8 = 0;
        let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
        v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
        lean_inc(v_a_4239_);
        lean_dec_ref_known(v___x_4238_, 1);
        v___x_4240_ = lean_unsigned_to_nat(1);
        v___x_4241_ = lean_mk_empty_array_with_capacity(v___x_4240_);
        v___x_4242_ = lean_array_push(v___x_4241_, v_x_4222_);
        v___x_4243_ = 1;
        v___x_4244_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4242_,
            v_a_4239_,
            v___x_4220_,
            v___x_4221_,
            v___x_4220_,
            v___x_4221_,
            v___x_4243_,
            v___y_4229_,
            v___y_4230_,
            v___y_4231_,
            v___y_4232_,
        );
        lean_dec_ref(v___x_4242_);
        return v___x_4244_;
    } else {
        lean_dec_ref(v_x_4222_);
        return v___x_4238_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_4245_: *mut LeanObject = *_args.add(0);
    let mut v_rhs_4246_: *mut LeanObject = *_args.add(1);
    let mut v_lhs_4247_: *mut LeanObject = *_args.add(2);
    let mut v___x_4248_: *mut LeanObject = *_args.add(3);
    let mut v___x_4249_: *mut LeanObject = *_args.add(4);
    let mut v_x_4250_: *mut LeanObject = *_args.add(5);
    let mut v___y_4251_: *mut LeanObject = *_args.add(6);
    let mut v___y_4252_: *mut LeanObject = *_args.add(7);
    let mut v___y_4253_: *mut LeanObject = *_args.add(8);
    let mut v___y_4254_: *mut LeanObject = *_args.add(9);
    let mut v___y_4255_: *mut LeanObject = *_args.add(10);
    let mut v___y_4256_: *mut LeanObject = *_args.add(11);
    let mut v___y_4257_: *mut LeanObject = *_args.add(12);
    let mut v___y_4258_: *mut LeanObject = *_args.add(13);
    let mut v___y_4259_: *mut LeanObject = *_args.add(14);
    let mut v___y_4260_: *mut LeanObject = *_args.add(15);
    let mut v___y_4261_: *mut LeanObject = *_args.add(16);
    let mut v___x_133262__boxed_4262_: u8 = 0;
    let mut v___x_133263__boxed_4263_: u8 = 0;
    let mut v_res_4264_: *mut LeanObject = core::ptr::null_mut();
    v___x_133262__boxed_4262_ = (lean_unbox(v___x_4248_) as u8);
    v___x_133263__boxed_4263_ = (lean_unbox(v___x_4249_) as u8);
    v_res_4264_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0(
            v_numArgs_4245_,
            v_rhs_4246_,
            v_lhs_4247_,
            v___x_133262__boxed_4262_,
            v___x_133263__boxed_4263_,
            v_x_4250_,
            v___y_4251_,
            v___y_4252_,
            v___y_4253_,
            v___y_4254_,
            v___y_4255_,
            v___y_4256_,
            v___y_4257_,
            v___y_4258_,
            v___y_4259_,
            v___y_4260_,
        );
    lean_dec(v___y_4260_);
    lean_dec_ref(v___y_4259_);
    lean_dec(v___y_4258_);
    lean_dec_ref(v___y_4257_);
    lean_dec(v___y_4256_);
    lean_dec_ref(v___y_4255_);
    lean_dec(v___y_4254_);
    lean_dec_ref(v___y_4253_);
    lean_dec(v___y_4252_);
    lean_dec(v___y_4251_);
    return v_res_4264_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(
    mut v_msg_4265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    v___x_4266_ = l_Lean_instInhabitedExpr;
    v___x_4267_ = lean_panic_fn_borrowed(v___x_4266_, v_msg_4265_);
    return v___x_4267_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(
    mut v_msgData_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    v___x_4274_ = lean_st_ref_get(v___y_4272_);
    v_env_4275_ = lean_ctor_get(v___x_4274_, 0);
    lean_inc_ref(v_env_4275_);
    lean_dec(v___x_4274_);
    v___x_4276_ = lean_st_ref_get(v___y_4270_);
    v_mctx_4277_ = lean_ctor_get(v___x_4276_, 0);
    lean_inc_ref(v_mctx_4277_);
    lean_dec(v___x_4276_);
    v_lctx_4278_ = lean_ctor_get(v___y_4269_, 2);
    v_options_4279_ = lean_ctor_get(v___y_4271_, 2);
    lean_inc_ref(v_options_4279_);
    lean_inc_ref(v_lctx_4278_);
    v___x_4280_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4280_, 0, v_env_4275_);
    lean_ctor_set(v___x_4280_, 1, v_mctx_4277_);
    lean_ctor_set(v___x_4280_, 2, v_lctx_4278_);
    lean_ctor_set(v___x_4280_, 3, v_options_4279_);
    v___x_4281_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4281_, 0, v___x_4280_);
    lean_ctor_set(v___x_4281_, 1, v_msgData_4268_);
    v___x_4282_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4282_, 0, v___x_4281_);
    return v___x_4282_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16___boxed(
    mut v_msgData_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4289_: *mut LeanObject = core::ptr::null_mut();
    v_res_4289_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msgData_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
    lean_dec(v___y_4287_);
    lean_dec_ref(v___y_4286_);
    lean_dec(v___y_4285_);
    lean_dec_ref(v___y_4284_);
    return v_res_4289_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(
    mut v_msg_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4296_ = lean_ctor_get(v___y_4293_, 5);
                v___x_4297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10_spec__16(v_msg_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
                v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
                v_isSharedCheck_4306_ = (!lean_is_exclusive(v___x_4297_)) as u8;
                if v_isSharedCheck_4306_ == 0 {
                    v___x_4300_ = v___x_4297_;
                    v_isShared_4301_ = v_isSharedCheck_4306_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4298_);
                    lean_dec(v___x_4297_);
                    v___x_4300_ = lean_box(0);
                    v_isShared_4301_ = v_isSharedCheck_4306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4296_);
                v___x_4302_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4302_, 0, v_ref_4296_);
                lean_ctor_set(v___x_4302_, 1, v_a_4298_);
                if v_isShared_4301_ == 0 {
                    lean_ctor_set_tag(v___x_4300_, 1);
                    lean_ctor_set(v___x_4300_, 0, v___x_4302_);
                    v___x_4304_ = v___x_4300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4302_);
                    v___x_4304_ = v_reuseFailAlloc_4305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg___boxed(
    mut v_msg_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4313_: *mut LeanObject = core::ptr::null_mut();
    v_res_4313_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
    lean_dec(v___y_4311_);
    lean_dec_ref(v___y_4310_);
    lean_dec(v___y_4309_);
    lean_dec_ref(v___y_4308_);
    return v_res_4313_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    v___x_4315_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__0;
    v___x_4316_ = l_Lean_stringToMessageData(v___x_4315_);
    return v___x_4316_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    v___x_4318_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__2;
    v___x_4319_ = l_Lean_stringToMessageData(v___x_4318_);
    return v___x_4319_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(
    mut v_lhs_4320_: *mut LeanObject,
    mut v_rhs_4321_: *mut LeanObject,
    mut v_00_u03b1_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    v___x_4334_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__1);
    v___x_4335_ = l_Lean_indentExpr(v_lhs_4320_);
    v___x_4336_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4336_, 0, v___x_4334_);
    lean_ctor_set(v___x_4336_, 1, v___x_4335_);
    v___x_4337_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___closed__3);
    v___x_4338_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4338_, 0, v___x_4336_);
    lean_ctor_set(v___x_4338_, 1, v___x_4337_);
    v___x_4339_ = l_Lean_indentExpr(v_rhs_4321_);
    v___x_4340_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4340_, 0, v___x_4338_);
    lean_ctor_set(v___x_4340_, 1, v___x_4339_);
    v___x_4341_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_4340_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
    return v___x_4341_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0___boxed(
    mut v_lhs_4342_: *mut LeanObject,
    mut v_rhs_4343_: *mut LeanObject,
    mut v_00_u03b1_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4356_: *mut LeanObject = core::ptr::null_mut();
    v_res_4356_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(
            v_lhs_4342_,
            v_rhs_4343_,
            v_00_u03b1_4344_,
            v___y_4345_,
            v___y_4346_,
            v___y_4347_,
            v___y_4348_,
            v___y_4349_,
            v___y_4350_,
            v___y_4351_,
            v___y_4352_,
            v___y_4353_,
            v___y_4354_,
        );
    lean_dec(v___y_4354_);
    lean_dec_ref(v___y_4353_);
    lean_dec(v___y_4352_);
    lean_dec_ref(v___y_4351_);
    lean_dec(v___y_4350_);
    lean_dec_ref(v___y_4349_);
    lean_dec(v___y_4348_);
    lean_dec_ref(v___y_4347_);
    lean_dec(v___y_4346_);
    lean_dec(v___y_4345_);
    return v_res_4356_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2()
-> *mut LeanObject {
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4359_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__1;
    v___x_4360_ = lean_unsigned_to_nat(4);
    v___x_4361_ = lean_unsigned_to_nat(198);
    v___x_4362_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__0;
    v___x_4363_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4364_ = l_mkPanicMessageWithDecl(
        v___x_4363_,
        v___x_4362_,
        v___x_4361_,
        v___x_4360_,
        v___x_4359_,
    );
    return v___x_4364_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2()
-> *mut LeanObject {
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    v___x_4367_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__1;
    v___x_4368_ = lean_unsigned_to_nat(4);
    v___x_4369_ = lean_unsigned_to_nat(318);
    v___x_4370_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0;
    v___x_4371_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4372_ = l_mkPanicMessageWithDecl(
        v___x_4371_,
        v___x_4370_,
        v___x_4369_,
        v___x_4368_,
        v___x_4367_,
    );
    return v___x_4372_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1() -> *mut LeanObject {
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4374_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_4375_ = lean_unsigned_to_nat(36);
    v___x_4376_ = lean_unsigned_to_nat(153);
    v___x_4377_ = l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0;
    v___x_4378_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4379_ = l_mkPanicMessageWithDecl(
        v___x_4378_,
        v___x_4377_,
        v___x_4376_,
        v___x_4375_,
        v___x_4374_,
    );
    return v___x_4379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2() -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_4381_ = lean_unsigned_to_nat(34);
    v___x_4382_ = lean_unsigned_to_nat(154);
    v___x_4383_ = l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0;
    v___x_4384_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4385_ = l_mkPanicMessageWithDecl(
        v___x_4384_,
        v___x_4383_,
        v___x_4382_,
        v___x_4381_,
        v___x_4380_,
    );
    return v___x_4385_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4() -> *mut LeanObject {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    v___x_4387_ = l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__3;
    v___x_4388_ = lean_unsigned_to_nat(4);
    v___x_4389_ = lean_unsigned_to_nat(155);
    v___x_4390_ = l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__0;
    v___x_4391_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4392_ = l_mkPanicMessageWithDecl(
        v___x_4391_,
        v___x_4390_,
        v___x_4389_,
        v___x_4388_,
        v___x_4387_,
    );
    return v___x_4392_;
}
pub unsafe fn l_Lean_Meta_Grind_mkEqCongrSymmProof(
    mut v_lhs_4405_: *mut LeanObject,
    mut v_rhs_4406_: *mut LeanObject,
    mut v_a_4407_: *mut LeanObject,
    mut v_a_4408_: *mut LeanObject,
    mut v_a_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
    mut v_a_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4445_: u8 = 0;
    let mut v___y_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4454_: u8 = 0;
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: u8 = 0;
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_fileName_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4500_: u8 = 0;
    let mut v_cancelTk_x3f_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4502_: u8 = 0;
    let mut v_inheritedTraceOptions_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v_arg_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v_arg_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    let mut v_arg_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: u8 = 0;
    let mut v_arg_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v_arg_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: u8 = 0;
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: u8 = 0;
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: u8 = 0;
    let mut v___x_4537_: u8 = 0;
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4488_ = lean_ctor_get(v_a_4415_, 0);
                v_fileMap_4489_ = lean_ctor_get(v_a_4415_, 1);
                v_options_4490_ = lean_ctor_get(v_a_4415_, 2);
                v_currRecDepth_4491_ = lean_ctor_get(v_a_4415_, 3);
                v_maxRecDepth_4492_ = lean_ctor_get(v_a_4415_, 4);
                v_ref_4493_ = lean_ctor_get(v_a_4415_, 5);
                v_currNamespace_4494_ = lean_ctor_get(v_a_4415_, 6);
                v_openDecls_4495_ = lean_ctor_get(v_a_4415_, 7);
                v_initHeartbeats_4496_ = lean_ctor_get(v_a_4415_, 8);
                v_maxHeartbeats_4497_ = lean_ctor_get(v_a_4415_, 9);
                v_quotContext_4498_ = lean_ctor_get(v_a_4415_, 10);
                v_currMacroScope_4499_ = lean_ctor_get(v_a_4415_, 11);
                v_diag_4500_ = lean_ctor_get_uint8(
                    v_a_4415_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4501_ = lean_ctor_get(v_a_4415_, 12);
                v_suppressElabErrors_4502_ = lean_ctor_get_uint8(
                    v_a_4415_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4503_ = lean_ctor_get(v_a_4415_, 13);
                v___x_4504_ = l_Lean_Expr_cleanupAnnotations(v_lhs_4405_);
                v___x_4505_ = l_Lean_Expr_isApp(v___x_4504_);
                v___x_4535_ = lean_unsigned_to_nat(0);
                v___x_4536_ = lean_nat_dec_eq(v_maxRecDepth_4492_, v___x_4535_);
                if v___x_4536_ == 0 {
                    v___x_4537_ = lean_nat_dec_eq(v_currRecDepth_4491_, v_maxRecDepth_4492_);
                    if v___x_4537_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        lean_dec_ref(v___x_4504_);
                        lean_dec_ref(v_rhs_4406_);
                        lean_inc(v_ref_4493_);
                        v___x_4538_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_4493_);
                        return v___x_4538_;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_4429_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1_once),
                    _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__1,
                );
                v___x_4430_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4429_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
                lean_dec_ref(v___y_4427_);
                return v___x_4430_;
            }
            2 => {
                v___x_4442_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2_once),
                    _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__2,
                );
                v___x_4443_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4442_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
                lean_dec_ref(v___y_4440_);
                return v___x_4443_;
            }
            3 => {
                if v___y_4454_ == 0 {
                    lean_dec_ref(v___y_4453_);
                    lean_dec_ref(v___y_4452_);
                    lean_dec_ref(v___y_4451_);
                    lean_dec_ref(v___y_4450_);
                    lean_dec_ref(v___y_4449_);
                    lean_dec_ref(v___y_4447_);
                    lean_dec_ref(v___y_4446_);
                    v___x_4455_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4_once
                        ),
                        _init_l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__4,
                    );
                    v___x_4456_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4455_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v___y_4448_, v_a_4416_);
                    lean_dec_ref(v___y_4448_);
                    return v___x_4456_;
                } else {
                    v___x_4457_ = l_Lean_Expr_constLevels_x21(v___y_4451_);
                    lean_dec_ref(v___y_4451_);
                    v___x_4458_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___y_4446_,
                            v___y_4453_,
                        );
                    if v___x_4458_ == 0 {
                        lean_inc_ref(v___y_4447_);
                        lean_inc_ref(v___y_4452_);
                        v___x_4459_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4452_, v___y_4447_, v___y_4445_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v___y_4448_, v_a_4416_);
                        if lean_obj_tag(v___x_4459_) == 0 {
                            v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
                            lean_inc(v_a_4460_);
                            lean_dec_ref_known(v___x_4459_, 1);
                            lean_inc_ref(v___y_4449_);
                            lean_inc_ref(v___y_4450_);
                            v___x_4461_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4450_, v___y_4449_, v___y_4445_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v___y_4448_, v_a_4416_);
                            lean_dec_ref(v___y_4448_);
                            if lean_obj_tag(v___x_4461_) == 0 {
                                v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
                                v_isSharedCheck_4472_ = (!lean_is_exclusive(v___x_4461_)) as u8;
                                if v_isSharedCheck_4472_ == 0 {
                                    v___x_4464_ = v___x_4461_;
                                    v_isShared_4465_ = v_isSharedCheck_4472_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4462_);
                                    lean_dec(v___x_4461_);
                                    v___x_4464_ = lean_box(0);
                                    v_isShared_4465_ = v_isSharedCheck_4472_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4460_);
                                lean_dec(v___x_4457_);
                                lean_dec_ref(v___y_4453_);
                                lean_dec_ref(v___y_4452_);
                                lean_dec_ref(v___y_4450_);
                                lean_dec_ref(v___y_4449_);
                                lean_dec_ref(v___y_4447_);
                                lean_dec_ref(v___y_4446_);
                                return v___x_4461_;
                            }
                        } else {
                            lean_dec(v___x_4457_);
                            lean_dec_ref(v___y_4453_);
                            lean_dec_ref(v___y_4452_);
                            lean_dec_ref(v___y_4450_);
                            lean_dec_ref(v___y_4449_);
                            lean_dec_ref(v___y_4448_);
                            lean_dec_ref(v___y_4447_);
                            lean_dec_ref(v___y_4446_);
                            return v___x_4459_;
                        }
                    } else {
                        lean_dec_ref(v___y_4453_);
                        v___x_4473_ = 0;
                        lean_inc_ref(v___y_4447_);
                        lean_inc_ref(v___y_4452_);
                        v___x_4474_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4452_, v___y_4447_, v___x_4473_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v___y_4448_, v_a_4416_);
                        if lean_obj_tag(v___x_4474_) == 0 {
                            v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
                            lean_inc(v_a_4475_);
                            lean_dec_ref_known(v___x_4474_, 1);
                            lean_inc_ref(v___y_4449_);
                            lean_inc_ref(v___y_4450_);
                            v___x_4476_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4450_, v___y_4449_, v___x_4473_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v___y_4448_, v_a_4416_);
                            lean_dec_ref(v___y_4448_);
                            if lean_obj_tag(v___x_4476_) == 0 {
                                v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
                                v_isSharedCheck_4487_ = (!lean_is_exclusive(v___x_4476_)) as u8;
                                if v_isSharedCheck_4487_ == 0 {
                                    v___x_4479_ = v___x_4476_;
                                    v_isShared_4480_ = v_isSharedCheck_4487_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4477_);
                                    lean_dec(v___x_4476_);
                                    v___x_4479_ = lean_box(0);
                                    v_isShared_4480_ = v_isSharedCheck_4487_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4475_);
                                lean_dec(v___x_4457_);
                                lean_dec_ref(v___y_4452_);
                                lean_dec_ref(v___y_4450_);
                                lean_dec_ref(v___y_4449_);
                                lean_dec_ref(v___y_4447_);
                                lean_dec_ref(v___y_4446_);
                                return v___x_4476_;
                            }
                        } else {
                            lean_dec(v___x_4457_);
                            lean_dec_ref(v___y_4452_);
                            lean_dec_ref(v___y_4450_);
                            lean_dec_ref(v___y_4449_);
                            lean_dec_ref(v___y_4448_);
                            lean_dec_ref(v___y_4447_);
                            lean_dec_ref(v___y_4446_);
                            return v___x_4474_;
                        }
                    }
                }
            }
            4 => {
                v___x_4466_ = l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__6;
                v___x_4467_ = l_Lean_mkConst(v___x_4466_, v___x_4457_);
                v___x_4468_ = l_Lean_mkApp8(
                    v___x_4467_,
                    v___y_4446_,
                    v___y_4453_,
                    v___y_4452_,
                    v___y_4450_,
                    v___y_4449_,
                    v___y_4447_,
                    v_a_4460_,
                    v_a_4462_,
                );
                if v_isShared_4465_ == 0 {
                    lean_ctor_set(v___x_4464_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4464_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4470_;
            }
            6 => {
                v___x_4481_ = l_Lean_Meta_Grind_mkEqCongrSymmProof___closed__8;
                v___x_4482_ = l_Lean_mkConst(v___x_4481_, v___x_4457_);
                v___x_4483_ = l_Lean_mkApp7(
                    v___x_4482_,
                    v___y_4446_,
                    v___y_4452_,
                    v___y_4450_,
                    v___y_4449_,
                    v___y_4447_,
                    v_a_4475_,
                    v_a_4477_,
                );
                if v_isShared_4480_ == 0 {
                    lean_ctor_set(v___x_4479_, 0, v___x_4483_);
                    v___x_4485_ = v___x_4479_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
                    v___x_4485_ = v_reuseFailAlloc_4486_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4485_;
            }
            8 => {
                v___x_4507_ = lean_unsigned_to_nat(1);
                v___x_4508_ = lean_nat_add(v_currRecDepth_4491_, v___x_4507_);
                lean_inc_ref(v_inheritedTraceOptions_4503_);
                lean_inc(v_cancelTk_x3f_4501_);
                lean_inc(v_currMacroScope_4499_);
                lean_inc(v_quotContext_4498_);
                lean_inc(v_maxHeartbeats_4497_);
                lean_inc(v_initHeartbeats_4496_);
                lean_inc(v_openDecls_4495_);
                lean_inc(v_currNamespace_4494_);
                lean_inc(v_ref_4493_);
                lean_inc(v_maxRecDepth_4492_);
                lean_inc_ref(v_options_4490_);
                lean_inc_ref(v_fileMap_4489_);
                lean_inc_ref(v_fileName_4488_);
                v___x_4509_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4509_, 0, v_fileName_4488_);
                lean_ctor_set(v___x_4509_, 1, v_fileMap_4489_);
                lean_ctor_set(v___x_4509_, 2, v_options_4490_);
                lean_ctor_set(v___x_4509_, 3, v___x_4508_);
                lean_ctor_set(v___x_4509_, 4, v_maxRecDepth_4492_);
                lean_ctor_set(v___x_4509_, 5, v_ref_4493_);
                lean_ctor_set(v___x_4509_, 6, v_currNamespace_4494_);
                lean_ctor_set(v___x_4509_, 7, v_openDecls_4495_);
                lean_ctor_set(v___x_4509_, 8, v_initHeartbeats_4496_);
                lean_ctor_set(v___x_4509_, 9, v_maxHeartbeats_4497_);
                lean_ctor_set(v___x_4509_, 10, v_quotContext_4498_);
                lean_ctor_set(v___x_4509_, 11, v_currMacroScope_4499_);
                lean_ctor_set(v___x_4509_, 12, v_cancelTk_x3f_4501_);
                lean_ctor_set(v___x_4509_, 13, v_inheritedTraceOptions_4503_);
                lean_ctor_set_uint8(
                    v___x_4509_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4500_,
                );
                lean_ctor_set_uint8(
                    v___x_4509_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4502_,
                );
                if v___x_4505_ == 0 {
                    lean_dec_ref(v___x_4504_);
                    lean_dec_ref(v_rhs_4406_);
                    v___y_4419_ = v_a_4407_;
                    v___y_4420_ = v_a_4408_;
                    v___y_4421_ = v_a_4409_;
                    v___y_4422_ = v_a_4410_;
                    v___y_4423_ = v_a_4411_;
                    v___y_4424_ = v_a_4412_;
                    v___y_4425_ = v_a_4413_;
                    v___y_4426_ = v_a_4414_;
                    v___y_4427_ = v___x_4509_;
                    v___y_4428_ = v_a_4416_;
                    state = 1;
                    continue;
                } else {
                    v_arg_4510_ = lean_ctor_get(v___x_4504_, 1);
                    lean_inc_ref(v_arg_4510_);
                    v___x_4511_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4504_);
                    v___x_4512_ = l_Lean_Expr_isApp(v___x_4511_);
                    if v___x_4512_ == 0 {
                        lean_dec_ref(v___x_4511_);
                        lean_dec_ref(v_arg_4510_);
                        lean_dec_ref(v_rhs_4406_);
                        v___y_4419_ = v_a_4407_;
                        v___y_4420_ = v_a_4408_;
                        v___y_4421_ = v_a_4409_;
                        v___y_4422_ = v_a_4410_;
                        v___y_4423_ = v_a_4411_;
                        v___y_4424_ = v_a_4412_;
                        v___y_4425_ = v_a_4413_;
                        v___y_4426_ = v_a_4414_;
                        v___y_4427_ = v___x_4509_;
                        v___y_4428_ = v_a_4416_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_4513_ = lean_ctor_get(v___x_4511_, 1);
                        lean_inc_ref(v_arg_4513_);
                        v___x_4514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4511_);
                        v___x_4515_ = l_Lean_Expr_isApp(v___x_4514_);
                        if v___x_4515_ == 0 {
                            lean_dec_ref(v___x_4514_);
                            lean_dec_ref(v_arg_4513_);
                            lean_dec_ref(v_arg_4510_);
                            lean_dec_ref(v_rhs_4406_);
                            v___y_4419_ = v_a_4407_;
                            v___y_4420_ = v_a_4408_;
                            v___y_4421_ = v_a_4409_;
                            v___y_4422_ = v_a_4410_;
                            v___y_4423_ = v_a_4411_;
                            v___y_4424_ = v_a_4412_;
                            v___y_4425_ = v_a_4413_;
                            v___y_4426_ = v_a_4414_;
                            v___y_4427_ = v___x_4509_;
                            v___y_4428_ = v_a_4416_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_4516_ = lean_ctor_get(v___x_4514_, 1);
                            lean_inc_ref(v_arg_4516_);
                            v___x_4517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4514_);
                            v___x_4518_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1;
                            v___x_4519_ = l_Lean_Expr_isConstOf(v___x_4517_, v___x_4518_);
                            if v___x_4519_ == 0 {
                                lean_dec_ref(v___x_4517_);
                                lean_dec_ref(v_arg_4516_);
                                lean_dec_ref(v_arg_4513_);
                                lean_dec_ref(v_arg_4510_);
                                lean_dec_ref(v_rhs_4406_);
                                v___y_4419_ = v_a_4407_;
                                v___y_4420_ = v_a_4408_;
                                v___y_4421_ = v_a_4409_;
                                v___y_4422_ = v_a_4410_;
                                v___y_4423_ = v_a_4411_;
                                v___y_4424_ = v_a_4412_;
                                v___y_4425_ = v_a_4413_;
                                v___y_4426_ = v_a_4414_;
                                v___y_4427_ = v___x_4509_;
                                v___y_4428_ = v_a_4416_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4520_ = l_Lean_Expr_cleanupAnnotations(v_rhs_4406_);
                                v___x_4521_ = l_Lean_Expr_isApp(v___x_4520_);
                                if v___x_4521_ == 0 {
                                    lean_dec_ref(v___x_4520_);
                                    lean_dec_ref(v___x_4517_);
                                    lean_dec_ref(v_arg_4516_);
                                    lean_dec_ref(v_arg_4513_);
                                    lean_dec_ref(v_arg_4510_);
                                    v___y_4432_ = v_a_4407_;
                                    v___y_4433_ = v_a_4408_;
                                    v___y_4434_ = v_a_4409_;
                                    v___y_4435_ = v_a_4410_;
                                    v___y_4436_ = v_a_4411_;
                                    v___y_4437_ = v_a_4412_;
                                    v___y_4438_ = v_a_4413_;
                                    v___y_4439_ = v_a_4414_;
                                    v___y_4440_ = v___x_4509_;
                                    v___y_4441_ = v_a_4416_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_4522_ = lean_ctor_get(v___x_4520_, 1);
                                    lean_inc_ref(v_arg_4522_);
                                    v___x_4523_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4520_);
                                    v___x_4524_ = l_Lean_Expr_isApp(v___x_4523_);
                                    if v___x_4524_ == 0 {
                                        lean_dec_ref(v___x_4523_);
                                        lean_dec_ref(v_arg_4522_);
                                        lean_dec_ref(v___x_4517_);
                                        lean_dec_ref(v_arg_4516_);
                                        lean_dec_ref(v_arg_4513_);
                                        lean_dec_ref(v_arg_4510_);
                                        v___y_4432_ = v_a_4407_;
                                        v___y_4433_ = v_a_4408_;
                                        v___y_4434_ = v_a_4409_;
                                        v___y_4435_ = v_a_4410_;
                                        v___y_4436_ = v_a_4411_;
                                        v___y_4437_ = v_a_4412_;
                                        v___y_4438_ = v_a_4413_;
                                        v___y_4439_ = v_a_4414_;
                                        v___y_4440_ = v___x_4509_;
                                        v___y_4441_ = v_a_4416_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_arg_4525_ = lean_ctor_get(v___x_4523_, 1);
                                        lean_inc_ref(v_arg_4525_);
                                        v___x_4526_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4523_);
                                        v___x_4527_ = l_Lean_Expr_isApp(v___x_4526_);
                                        if v___x_4527_ == 0 {
                                            lean_dec_ref(v___x_4526_);
                                            lean_dec_ref(v_arg_4525_);
                                            lean_dec_ref(v_arg_4522_);
                                            lean_dec_ref(v___x_4517_);
                                            lean_dec_ref(v_arg_4516_);
                                            lean_dec_ref(v_arg_4513_);
                                            lean_dec_ref(v_arg_4510_);
                                            v___y_4432_ = v_a_4407_;
                                            v___y_4433_ = v_a_4408_;
                                            v___y_4434_ = v_a_4409_;
                                            v___y_4435_ = v_a_4410_;
                                            v___y_4436_ = v_a_4411_;
                                            v___y_4437_ = v_a_4412_;
                                            v___y_4438_ = v_a_4413_;
                                            v___y_4439_ = v_a_4414_;
                                            v___y_4440_ = v___x_4509_;
                                            v___y_4441_ = v_a_4416_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v_arg_4528_ = lean_ctor_get(v___x_4526_, 1);
                                            lean_inc_ref(v_arg_4528_);
                                            v___x_4529_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_4526_);
                                            v___x_4530_ =
                                                l_Lean_Expr_isConstOf(v___x_4529_, v___x_4518_);
                                            lean_dec_ref(v___x_4529_);
                                            if v___x_4530_ == 0 {
                                                lean_dec_ref(v_arg_4528_);
                                                lean_dec_ref(v_arg_4525_);
                                                lean_dec_ref(v_arg_4522_);
                                                lean_dec_ref(v___x_4517_);
                                                lean_dec_ref(v_arg_4516_);
                                                lean_dec_ref(v_arg_4513_);
                                                lean_dec_ref(v_arg_4510_);
                                                v___y_4432_ = v_a_4407_;
                                                v___y_4433_ = v_a_4408_;
                                                v___y_4434_ = v_a_4409_;
                                                v___y_4435_ = v_a_4410_;
                                                v___y_4436_ = v_a_4411_;
                                                v___y_4437_ = v_a_4412_;
                                                v___y_4438_ = v_a_4413_;
                                                v___y_4439_ = v_a_4414_;
                                                v___y_4440_ = v___x_4509_;
                                                v___y_4441_ = v_a_4416_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_4531_ = lean_st_ref_get(v_a_4407_);
                                                v___x_4532_ = lean_st_ref_get(v_a_4407_);
                                                v___x_4533_ = l_Lean_Meta_Grind_Goal_hasSameRoot(
                                                    v___x_4531_,
                                                    v_arg_4513_,
                                                    v_arg_4522_,
                                                );
                                                lean_dec(v___x_4531_);
                                                if v___x_4533_ == 0 {
                                                    lean_dec(v___x_4532_);
                                                    v___y_4445_ = v___x_4530_;
                                                    v___y_4446_ = v_arg_4516_;
                                                    v___y_4447_ = v_arg_4522_;
                                                    v___y_4448_ = v___x_4509_;
                                                    v___y_4449_ = v_arg_4525_;
                                                    v___y_4450_ = v_arg_4510_;
                                                    v___y_4451_ = v___x_4517_;
                                                    v___y_4452_ = v_arg_4513_;
                                                    v___y_4453_ = v_arg_4528_;
                                                    v___y_4454_ = v___x_4533_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    v___x_4534_ =
                                                        l_Lean_Meta_Grind_Goal_hasSameRoot(
                                                            v___x_4532_,
                                                            v_arg_4510_,
                                                            v_arg_4525_,
                                                        );
                                                    lean_dec(v___x_4532_);
                                                    v___y_4445_ = v___x_4530_;
                                                    v___y_4446_ = v_arg_4516_;
                                                    v___y_4447_ = v_arg_4522_;
                                                    v___y_4448_ = v___x_4509_;
                                                    v___y_4449_ = v_arg_4525_;
                                                    v___y_4450_ = v_arg_4510_;
                                                    v___y_4451_ = v___x_4517_;
                                                    v___y_4452_ = v_arg_4513_;
                                                    v___y_4453_ = v_arg_4528_;
                                                    v___y_4454_ = v___x_4534_;
                                                    state = 3;
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
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2()
-> u64 {
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: u64 = 0;
    v___x_4542_ = 1;
    v___x_4543_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4542_);
    return v___x_4543_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4()
-> *mut LeanObject {
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    v___x_4545_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_4546_ = lean_unsigned_to_nat(38);
    v___x_4547_ = lean_unsigned_to_nat(250);
    v___x_4548_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3;
    v___x_4549_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4550_ = l_mkPanicMessageWithDecl(
        v___x_4549_,
        v___x_4548_,
        v___x_4547_,
        v___x_4546_,
        v___x_4545_,
    );
    return v___x_4550_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6()
-> *mut LeanObject {
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4552_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__5;
    v___x_4553_ = lean_unsigned_to_nat(6);
    v___x_4554_ = lean_unsigned_to_nat(260);
    v___x_4555_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__3;
    v___x_4556_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4557_ = l_mkPanicMessageWithDecl(
        v___x_4556_,
        v___x_4555_,
        v___x_4554_,
        v___x_4553_,
        v___x_4552_,
    );
    return v___x_4557_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2()
-> *mut LeanObject {
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    v___x_4560_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__1;
    v___x_4561_ = lean_unsigned_to_nat(4);
    v___x_4562_ = lean_unsigned_to_nat(219);
    v___x_4563_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__0;
    v___x_4564_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4565_ = l_mkPanicMessageWithDecl(
        v___x_4564_,
        v___x_4563_,
        v___x_4562_,
        v___x_4561_,
        v___x_4560_,
    );
    return v___x_4565_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(
    mut v_lhs_4566_: *mut LeanObject,
    mut v_rhs_4567_: *mut LeanObject,
    mut v_heq_4568_: u8,
    mut v_a_4569_: *mut LeanObject,
    mut v_a_4570_: *mut LeanObject,
    mut v_a_4571_: *mut LeanObject,
    mut v_a_4572_: *mut LeanObject,
    mut v_a_4573_: *mut LeanObject,
    mut v_a_4574_: *mut LeanObject,
    mut v_a_4575_: *mut LeanObject,
    mut v_a_4576_: *mut LeanObject,
    mut v_a_4577_: *mut LeanObject,
    mut v_a_4578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: u8 = 0;
    let mut v_g_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4614_: u8 = 0;
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: u8 = 0;
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numArgs_4580_ = l_Lean_Expr_getAppNumArgs(v_lhs_4566_);
                v___x_4581_ = l_Lean_Expr_getAppNumArgs(v_rhs_4567_);
                v___x_4582_ = lean_nat_dec_eq(v___x_4581_, v_numArgs_4580_);
                lean_dec(v___x_4581_);
                if v___x_4582_ == 0 {
                    lean_dec(v_numArgs_4580_);
                    lean_dec_ref(v_rhs_4567_);
                    lean_dec_ref(v_lhs_4566_);
                    v___x_4583_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___closed__2);
                    v___x_4584_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4583_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
                    return v___x_4584_;
                } else {
                    v_f_4585_ = l_Lean_Expr_getAppFn(v_lhs_4566_);
                    v___x_4586_ = lean_box(0);
                    lean_inc_ref(v_f_4585_);
                    v___x_4587_ = l_Lean_Meta_getFunInfo(
                        v_f_4585_,
                        v___x_4586_,
                        v_a_4575_,
                        v_a_4576_,
                        v_a_4577_,
                        v_a_4578_,
                    );
                    if lean_obj_tag(v___x_4587_) == 0 {
                        v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
                        lean_inc(v_a_4588_);
                        lean_dec_ref_known(v___x_4587_, 1);
                        v___x_4589_ = l_Lean_Meta_FunInfo_getArity(v_a_4588_);
                        lean_dec(v_a_4588_);
                        v___x_4590_ = lean_nat_dec_lt(v___x_4589_, v_numArgs_4580_);
                        lean_dec(v___x_4589_);
                        if v___x_4590_ == 0 {
                            v_g_4591_ = l_Lean_Expr_getAppFn(v_rhs_4567_);
                            v___x_4592_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_f_4585_, v_g_4591_, v_numArgs_4580_, v_lhs_4566_, v_rhs_4567_, v_heq_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
                            return v___x_4592_;
                        } else {
                            lean_dec_ref(v_f_4585_);
                            lean_dec(v_numArgs_4580_);
                            lean_inc_ref(v_lhs_4566_);
                            v___x_4593_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommonPrefix(v_lhs_4566_, v_rhs_4567_);
                            if lean_obj_tag(v___x_4593_) == 1 {
                                v_val_4594_ = lean_ctor_get(v___x_4593_, 0);
                                lean_inc(v_val_4594_);
                                lean_dec_ref_known(v___x_4593_, 1);
                                v_fst_4595_ = lean_ctor_get(v_val_4594_, 0);
                                lean_inc(v_fst_4595_);
                                v_snd_4596_ = lean_ctor_get(v_val_4594_, 1);
                                lean_inc_n(v_snd_4596_, 2);
                                lean_dec(v_val_4594_);
                                v___x_4611_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(
                                    v_fst_4595_,
                                    v_snd_4596_,
                                    v_a_4572_,
                                    v_a_4575_,
                                    v_a_4576_,
                                    v_a_4577_,
                                    v_a_4578_,
                                );
                                if lean_obj_tag(v___x_4611_) == 0 {
                                    v___y_4598_ = v___x_4611_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
                                    lean_inc(v_a_4612_);
                                    v___x_4616_ = l_Lean_Exception_isInterrupt(v_a_4612_);
                                    if v___x_4616_ == 0 {
                                        v___x_4617_ = l_Lean_Exception_isRuntime(v_a_4612_);
                                        v___y_4614_ = v___x_4617_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v_a_4612_);
                                        v___y_4614_ = v___x_4616_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_4593_);
                                v___x_4618_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_4566_, v_rhs_4567_, lean_box(0), v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
                                return v___x_4618_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_f_4585_);
                        lean_dec(v_numArgs_4580_);
                        lean_dec_ref(v_rhs_4567_);
                        lean_dec_ref(v_lhs_4566_);
                        v_a_4619_ = lean_ctor_get(v___x_4587_, 0);
                        v_isSharedCheck_4626_ = (!lean_is_exclusive(v___x_4587_)) as u8;
                        if v_isSharedCheck_4626_ == 0 {
                            v___x_4621_ = v___x_4587_;
                            v_isShared_4622_ = v_isSharedCheck_4626_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4619_);
                            lean_dec(v___x_4587_);
                            v___x_4621_ = lean_box(0);
                            v_isShared_4622_ = v_isSharedCheck_4626_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4598_) == 0 {
                    v_a_4599_ = lean_ctor_get(v___y_4598_, 0);
                    lean_inc(v_a_4599_);
                    lean_dec_ref_known(v___y_4598_, 1);
                    v___x_4600_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_4599_, v_lhs_4566_, v_rhs_4567_, v_snd_4596_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
                    lean_dec(v_snd_4596_);
                    lean_dec_ref(v_rhs_4567_);
                    lean_dec_ref(v_lhs_4566_);
                    lean_dec(v_a_4599_);
                    if lean_obj_tag(v___x_4600_) == 0 {
                        v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
                        lean_inc(v_a_4601_);
                        lean_dec_ref_known(v___x_4600_, 1);
                        v___x_4602_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_4601_, v_heq_4568_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
                        return v___x_4602_;
                    } else {
                        return v___x_4600_;
                    }
                } else {
                    lean_dec(v_snd_4596_);
                    lean_dec_ref(v_rhs_4567_);
                    lean_dec_ref(v_lhs_4566_);
                    v_a_4603_ = lean_ctor_get(v___y_4598_, 0);
                    v_isSharedCheck_4610_ = (!lean_is_exclusive(v___y_4598_)) as u8;
                    if v_isSharedCheck_4610_ == 0 {
                        v___x_4605_ = v___y_4598_;
                        v_isShared_4606_ = v_isSharedCheck_4610_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4603_);
                        lean_dec(v___y_4598_);
                        v___x_4605_ = lean_box(0);
                        v_isShared_4606_ = v_isSharedCheck_4610_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4606_ == 0 {
                    v___x_4608_ = v___x_4605_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4608_;
            }
            4 => {
                if v___y_4614_ == 0 {
                    lean_dec_ref_known(v___x_4611_, 1);
                    lean_inc_ref(v_rhs_4567_);
                    lean_inc_ref(v_lhs_4566_);
                    v___x_4615_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___lam__0(v_lhs_4566_, v_rhs_4567_, lean_box(0), v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
                    v___y_4598_ = v___x_4615_;
                    state = 1;
                    continue;
                } else {
                    v___y_4598_ = v___x_4611_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(
    mut v_lhs_4627_: *mut LeanObject,
    mut v_rhs_4628_: *mut LeanObject,
    mut v_a_4629_: *mut LeanObject,
    mut v_a_4630_: *mut LeanObject,
    mut v_a_4631_: *mut LeanObject,
    mut v_a_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
    mut v_a_4638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v_a_u2081_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_u2082_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4655_: u8 = 0;
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_a_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4674_: u8 = 0;
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v_a_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_a_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_isSharedCheck_4707_: u8 = 0;
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4720_: u8 = 0;
    let mut v_a_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4724_: u8 = 0;
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4728_: u8 = 0;
    let mut v_a_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4732_: u8 = 0;
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4640_ = l_Lean_Expr_isApp(v_lhs_4627_);
                if v___x_4640_ == 0 {
                    v___x_4641_ = lean_box(0);
                    v___x_4642_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4642_, 0, v___x_4641_);
                    return v___x_4642_;
                } else {
                    v___x_4643_ = l_Lean_Expr_appFn_x21(v_lhs_4627_);
                    v___x_4644_ = l_Lean_Expr_appFn_x21(v_rhs_4628_);
                    v___x_4645_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v___x_4643_, v___x_4644_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
                    lean_dec_ref(v___x_4644_);
                    if lean_obj_tag(v___x_4645_) == 0 {
                        v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
                        v_isSharedCheck_4741_ = (!lean_is_exclusive(v___x_4645_)) as u8;
                        if v_isSharedCheck_4741_ == 0 {
                            v___x_4648_ = v___x_4645_;
                            v_isShared_4649_ = v_isSharedCheck_4741_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4646_);
                            lean_dec(v___x_4645_);
                            v___x_4648_ = lean_box(0);
                            v_isShared_4649_ = v_isSharedCheck_4741_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4643_);
                        return v___x_4645_;
                    }
                }
            }
            1 => {
                v_a_u2081_4650_ = l_Lean_Expr_appArg_x21(v_lhs_4627_);
                v_a_u2082_4651_ = l_Lean_Expr_appArg_x21(v_rhs_4628_);
                if lean_obj_tag(v_a_4646_) == 1 {
                    lean_del_object(v___x_4648_);
                    lean_dec_ref(v___x_4643_);
                    v_val_4652_ = lean_ctor_get(v_a_4646_, 0);
                    v_isSharedCheck_4707_ = (!lean_is_exclusive(v_a_4646_)) as u8;
                    if v_isSharedCheck_4707_ == 0 {
                        v___x_4654_ = v_a_4646_;
                        v_isShared_4655_ = v_isSharedCheck_4707_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4652_);
                        lean_dec(v_a_4646_);
                        v___x_4654_ = lean_box(0);
                        v_isShared_4655_ = v_isSharedCheck_4707_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4646_);
                    v___x_4708_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_u2081_4650_,
                            v_a_u2082_4651_,
                        );
                    if v___x_4708_ == 0 {
                        lean_del_object(v___x_4648_);
                        v___x_4709_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_a_u2081_4650_, v_a_u2082_4651_, v___x_4708_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
                        if lean_obj_tag(v___x_4709_) == 0 {
                            v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
                            lean_inc(v_a_4710_);
                            lean_dec_ref_known(v___x_4709_, 1);
                            v___x_4711_ = l_Lean_Meta_mkCongrArg(
                                v___x_4643_,
                                v_a_4710_,
                                v_a_4635_,
                                v_a_4636_,
                                v_a_4637_,
                                v_a_4638_,
                            );
                            if lean_obj_tag(v___x_4711_) == 0 {
                                v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
                                v_isSharedCheck_4720_ = (!lean_is_exclusive(v___x_4711_)) as u8;
                                if v_isSharedCheck_4720_ == 0 {
                                    v___x_4714_ = v___x_4711_;
                                    v_isShared_4715_ = v_isSharedCheck_4720_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_4712_);
                                    lean_dec(v___x_4711_);
                                    v___x_4714_ = lean_box(0);
                                    v_isShared_4715_ = v_isSharedCheck_4720_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                v_a_4721_ = lean_ctor_get(v___x_4711_, 0);
                                v_isSharedCheck_4728_ = (!lean_is_exclusive(v___x_4711_)) as u8;
                                if v_isSharedCheck_4728_ == 0 {
                                    v___x_4723_ = v___x_4711_;
                                    v_isShared_4724_ = v_isSharedCheck_4728_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_4721_);
                                    lean_dec(v___x_4711_);
                                    v___x_4723_ = lean_box(0);
                                    v_isShared_4724_ = v_isSharedCheck_4728_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4643_);
                            v_a_4729_ = lean_ctor_get(v___x_4709_, 0);
                            v_isSharedCheck_4736_ = (!lean_is_exclusive(v___x_4709_)) as u8;
                            if v_isSharedCheck_4736_ == 0 {
                                v___x_4731_ = v___x_4709_;
                                v_isShared_4732_ = v_isSharedCheck_4736_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_4729_);
                                lean_dec(v___x_4709_);
                                v___x_4731_ = lean_box(0);
                                v_isShared_4732_ = v_isSharedCheck_4736_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_a_u2082_4651_);
                        lean_dec_ref(v_a_u2081_4650_);
                        lean_dec_ref(v___x_4643_);
                        v___x_4737_ = lean_box(0);
                        if v_isShared_4649_ == 0 {
                            lean_ctor_set(v___x_4648_, 0, v___x_4737_);
                            v___x_4739_ = v___x_4648_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4737_);
                            v___x_4739_ = v_reuseFailAlloc_4740_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4656_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_a_u2081_4650_,
                        v_a_u2082_4651_,
                    );
                if v___x_4656_ == 0 {
                    v___x_4657_ =
                        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
                            v_a_u2081_4650_,
                            v_a_u2082_4651_,
                            v___x_4656_,
                            v_a_4629_,
                            v_a_4630_,
                            v_a_4631_,
                            v_a_4632_,
                            v_a_4633_,
                            v_a_4634_,
                            v_a_4635_,
                            v_a_4636_,
                            v_a_4637_,
                            v_a_4638_,
                        );
                    if lean_obj_tag(v___x_4657_) == 0 {
                        v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
                        lean_inc(v_a_4658_);
                        lean_dec_ref_known(v___x_4657_, 1);
                        v___x_4659_ = l_Lean_Meta_mkCongr(
                            v_val_4652_,
                            v_a_4658_,
                            v_a_4635_,
                            v_a_4636_,
                            v_a_4637_,
                            v_a_4638_,
                        );
                        if lean_obj_tag(v___x_4659_) == 0 {
                            v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
                            v_isSharedCheck_4670_ = (!lean_is_exclusive(v___x_4659_)) as u8;
                            if v_isSharedCheck_4670_ == 0 {
                                v___x_4662_ = v___x_4659_;
                                v_isShared_4663_ = v_isSharedCheck_4670_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4660_);
                                lean_dec(v___x_4659_);
                                v___x_4662_ = lean_box(0);
                                v_isShared_4663_ = v_isSharedCheck_4670_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4654_);
                            v_a_4671_ = lean_ctor_get(v___x_4659_, 0);
                            v_isSharedCheck_4678_ = (!lean_is_exclusive(v___x_4659_)) as u8;
                            if v_isSharedCheck_4678_ == 0 {
                                v___x_4673_ = v___x_4659_;
                                v_isShared_4674_ = v_isSharedCheck_4678_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4671_);
                                lean_dec(v___x_4659_);
                                v___x_4673_ = lean_box(0);
                                v_isShared_4674_ = v_isSharedCheck_4678_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4654_);
                        lean_dec(v_val_4652_);
                        v_a_4679_ = lean_ctor_get(v___x_4657_, 0);
                        v_isSharedCheck_4686_ = (!lean_is_exclusive(v___x_4657_)) as u8;
                        if v_isSharedCheck_4686_ == 0 {
                            v___x_4681_ = v___x_4657_;
                            v_isShared_4682_ = v_isSharedCheck_4686_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4679_);
                            lean_dec(v___x_4657_);
                            v___x_4681_ = lean_box(0);
                            v_isShared_4682_ = v_isSharedCheck_4686_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_u2082_4651_);
                    v___x_4687_ = l_Lean_Meta_mkCongrFun(
                        v_val_4652_,
                        v_a_u2081_4650_,
                        v_a_4635_,
                        v_a_4636_,
                        v_a_4637_,
                        v_a_4638_,
                    );
                    if lean_obj_tag(v___x_4687_) == 0 {
                        v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
                        v_isSharedCheck_4698_ = (!lean_is_exclusive(v___x_4687_)) as u8;
                        if v_isSharedCheck_4698_ == 0 {
                            v___x_4690_ = v___x_4687_;
                            v_isShared_4691_ = v_isSharedCheck_4698_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4688_);
                            lean_dec(v___x_4687_);
                            v___x_4690_ = lean_box(0);
                            v_isShared_4691_ = v_isSharedCheck_4698_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4654_);
                        v_a_4699_ = lean_ctor_get(v___x_4687_, 0);
                        v_isSharedCheck_4706_ = (!lean_is_exclusive(v___x_4687_)) as u8;
                        if v_isSharedCheck_4706_ == 0 {
                            v___x_4701_ = v___x_4687_;
                            v_isShared_4702_ = v_isSharedCheck_4706_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4699_);
                            lean_dec(v___x_4687_);
                            v___x_4701_ = lean_box(0);
                            v_isShared_4702_ = v_isSharedCheck_4706_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_4655_ == 0 {
                    lean_ctor_set(v___x_4654_, 0, v_a_4660_);
                    v___x_4665_ = v___x_4654_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4660_);
                    v___x_4665_ = v_reuseFailAlloc_4669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4663_ == 0 {
                    lean_ctor_set(v___x_4662_, 0, v___x_4665_);
                    v___x_4667_ = v___x_4662_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4665_);
                    v___x_4667_ = v_reuseFailAlloc_4668_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4667_;
            }
            6 => {
                if v_isShared_4674_ == 0 {
                    v___x_4676_ = v___x_4673_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
                    v___x_4676_ = v_reuseFailAlloc_4677_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4676_;
            }
            8 => {
                if v_isShared_4682_ == 0 {
                    v___x_4684_ = v___x_4681_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
                    v___x_4684_ = v_reuseFailAlloc_4685_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4684_;
            }
            10 => {
                if v_isShared_4655_ == 0 {
                    lean_ctor_set(v___x_4654_, 0, v_a_4688_);
                    v___x_4693_ = v___x_4654_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4688_);
                    v___x_4693_ = v_reuseFailAlloc_4697_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4691_ == 0 {
                    lean_ctor_set(v___x_4690_, 0, v___x_4693_);
                    v___x_4695_ = v___x_4690_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4695_;
            }
            13 => {
                if v_isShared_4702_ == 0 {
                    v___x_4704_ = v___x_4701_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
                    v___x_4704_ = v_reuseFailAlloc_4705_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4704_;
            }
            15 => {
                v___x_4716_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4716_, 0, v_a_4712_);
                if v_isShared_4715_ == 0 {
                    lean_ctor_set(v___x_4714_, 0, v___x_4716_);
                    v___x_4718_ = v___x_4714_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4716_);
                    v___x_4718_ = v_reuseFailAlloc_4719_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4718_;
            }
            17 => {
                if v_isShared_4724_ == 0 {
                    v___x_4726_ = v___x_4723_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
                    v___x_4726_ = v_reuseFailAlloc_4727_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4726_;
            }
            19 => {
                if v_isShared_4732_ == 0 {
                    v___x_4734_ = v___x_4731_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
                    v___x_4734_ = v_reuseFailAlloc_4735_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4734_;
            }
            21 => {
                return v___x_4739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3()
-> *mut LeanObject {
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    v___x_4745_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__2;
    v___x_4746_ = lean_unsigned_to_nat(14);
    v___x_4747_ = lean_unsigned_to_nat(22);
    v___x_4748_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__1;
    v___x_4749_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__0;
    v___x_4750_ = l_mkPanicMessageWithDecl(
        v___x_4749_,
        v___x_4748_,
        v___x_4747_,
        v___x_4746_,
        v___x_4745_,
    );
    return v___x_4750_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(
    mut v_lhs_4751_: *mut LeanObject,
    mut v_rhs_4752_: *mut LeanObject,
    mut v_heq_4753_: u8,
    mut v_a_4754_: *mut LeanObject,
    mut v_a_4755_: *mut LeanObject,
    mut v_a_4756_: *mut LeanObject,
    mut v_a_4757_: *mut LeanObject,
    mut v_a_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
    mut v_a_4762_: *mut LeanObject,
    mut v_a_4763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___y_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut v_a_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4783_: u8 = 0;
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4765_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(v_lhs_4751_, v_rhs_4752_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
                if lean_obj_tag(v___x_4765_) == 0 {
                    v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
                    v_isSharedCheck_4779_ = (!lean_is_exclusive(v___x_4765_)) as u8;
                    if v_isSharedCheck_4779_ == 0 {
                        v___x_4768_ = v___x_4765_;
                        v_isShared_4769_ = v_isSharedCheck_4779_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4766_);
                        lean_dec(v___x_4765_);
                        v___x_4768_ = lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4779_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4780_ = lean_ctor_get(v___x_4765_, 0);
                    v_isSharedCheck_4787_ = (!lean_is_exclusive(v___x_4765_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v___x_4782_ = v___x_4765_;
                        v_isShared_4783_ = v_isSharedCheck_4787_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4780_);
                        lean_dec(v___x_4765_);
                        v___x_4782_ = lean_box(0);
                        v_isShared_4783_ = v_isSharedCheck_4787_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4766_) == 0 {
                    v___x_4776_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___closed__3);
                    v___x_4777_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_spec__13(v___x_4776_);
                    v___y_4771_ = v___x_4777_;
                    state = 2;
                    continue;
                } else {
                    v_val_4778_ = lean_ctor_get(v_a_4766_, 0);
                    lean_inc(v_val_4778_);
                    lean_dec_ref_known(v_a_4766_, 1);
                    v___y_4771_ = v_val_4778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_heq_4753_ == 0 {
                    if v_isShared_4769_ == 0 {
                        lean_ctor_set(v___x_4768_, 0, v___y_4771_);
                        v___x_4773_ = v___x_4768_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___y_4771_);
                        v___x_4773_ = v_reuseFailAlloc_4774_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4768_);
                    v___x_4775_ = l_Lean_Meta_mkHEqOfEq(
                        v___y_4771_,
                        v_a_4760_,
                        v_a_4761_,
                        v_a_4762_,
                        v_a_4763_,
                    );
                    return v___x_4775_;
                }
            }
            3 => {
                return v___x_4773_;
            }
            4 => {
                if v_isShared_4783_ == 0 {
                    v___x_4785_ = v___x_4782_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1() -> *mut LeanObject {
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    v___x_4789_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_4790_ = lean_unsigned_to_nat(36);
    v___x_4791_ = lean_unsigned_to_nat(143);
    v___x_4792_ = l_Lean_Meta_Grind_mkEqCongrProof___closed__0;
    v___x_4793_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4794_ = l_mkPanicMessageWithDecl(
        v___x_4793_,
        v___x_4792_,
        v___x_4791_,
        v___x_4790_,
        v___x_4789_,
    );
    return v___x_4794_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2() -> *mut LeanObject {
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    v___x_4795_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_4796_ = lean_unsigned_to_nat(34);
    v___x_4797_ = lean_unsigned_to_nat(144);
    v___x_4798_ = l_Lean_Meta_Grind_mkEqCongrProof___closed__0;
    v___x_4799_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4800_ = l_mkPanicMessageWithDecl(
        v___x_4799_,
        v___x_4798_,
        v___x_4797_,
        v___x_4796_,
        v___x_4795_,
    );
    return v___x_4800_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4() -> *mut LeanObject {
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    v___x_4802_ = l_Lean_Meta_Grind_mkEqCongrProof___closed__3;
    v___x_4803_ = lean_unsigned_to_nat(4);
    v___x_4804_ = lean_unsigned_to_nat(145);
    v___x_4805_ = l_Lean_Meta_Grind_mkEqCongrProof___closed__0;
    v___x_4806_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_4807_ = l_mkPanicMessageWithDecl(
        v___x_4806_,
        v___x_4805_,
        v___x_4804_,
        v___x_4803_,
        v___x_4802_,
    );
    return v___x_4807_;
}
pub unsafe fn l_Lean_Meta_Grind_mkEqCongrProof(
    mut v_lhs_4818_: *mut LeanObject,
    mut v_rhs_4819_: *mut LeanObject,
    mut v_a_4820_: *mut LeanObject,
    mut v_a_4821_: *mut LeanObject,
    mut v_a_4822_: *mut LeanObject,
    mut v_a_4823_: *mut LeanObject,
    mut v_a_4824_: *mut LeanObject,
    mut v_a_4825_: *mut LeanObject,
    mut v_a_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
    mut v_a_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4861_: u8 = 0;
    let mut v___y_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4867_: u8 = 0;
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4885_: u8 = 0;
    let mut v___x_4886_: u8 = 0;
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4893_: u8 = 0;
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4900_: u8 = 0;
    let mut v_fileName_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4913_: u8 = 0;
    let mut v_cancelTk_x3f_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4915_: u8 = 0;
    let mut v_inheritedTraceOptions_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: u8 = 0;
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: u8 = 0;
    let mut v_arg_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: u8 = 0;
    let mut v_arg_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: u8 = 0;
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: u8 = 0;
    let mut v_arg_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    let mut v_arg_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: u8 = 0;
    let mut v_arg_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: u8 = 0;
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: u8 = 0;
    let mut v___x_4950_: u8 = 0;
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4901_ = lean_ctor_get(v_a_4828_, 0);
                v_fileMap_4902_ = lean_ctor_get(v_a_4828_, 1);
                v_options_4903_ = lean_ctor_get(v_a_4828_, 2);
                v_currRecDepth_4904_ = lean_ctor_get(v_a_4828_, 3);
                v_maxRecDepth_4905_ = lean_ctor_get(v_a_4828_, 4);
                v_ref_4906_ = lean_ctor_get(v_a_4828_, 5);
                v_currNamespace_4907_ = lean_ctor_get(v_a_4828_, 6);
                v_openDecls_4908_ = lean_ctor_get(v_a_4828_, 7);
                v_initHeartbeats_4909_ = lean_ctor_get(v_a_4828_, 8);
                v_maxHeartbeats_4910_ = lean_ctor_get(v_a_4828_, 9);
                v_quotContext_4911_ = lean_ctor_get(v_a_4828_, 10);
                v_currMacroScope_4912_ = lean_ctor_get(v_a_4828_, 11);
                v_diag_4913_ = lean_ctor_get_uint8(
                    v_a_4828_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4914_ = lean_ctor_get(v_a_4828_, 12);
                v_suppressElabErrors_4915_ = lean_ctor_get_uint8(
                    v_a_4828_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4916_ = lean_ctor_get(v_a_4828_, 13);
                v___x_4917_ = l_Lean_Expr_cleanupAnnotations(v_lhs_4818_);
                v___x_4918_ = l_Lean_Expr_isApp(v___x_4917_);
                v___x_4948_ = lean_unsigned_to_nat(0);
                v___x_4949_ = lean_nat_dec_eq(v_maxRecDepth_4905_, v___x_4948_);
                if v___x_4949_ == 0 {
                    v___x_4950_ = lean_nat_dec_eq(v_currRecDepth_4904_, v_maxRecDepth_4905_);
                    if v___x_4950_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        lean_dec_ref(v___x_4917_);
                        lean_dec_ref(v_rhs_4819_);
                        lean_inc(v_ref_4906_);
                        v___x_4951_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(v_ref_4906_);
                        return v___x_4951_;
                    }
                } else {
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_4842_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrProof___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrProof___closed__1_once),
                    _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__1,
                );
                v___x_4843_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4842_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
                lean_dec_ref(v___y_4840_);
                return v___x_4843_;
            }
            2 => {
                v___x_4855_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrProof___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrProof___closed__2_once),
                    _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__2,
                );
                v___x_4856_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4855_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
                lean_dec_ref(v___y_4853_);
                return v___x_4856_;
            }
            3 => {
                if v___y_4867_ == 0 {
                    lean_dec_ref(v___y_4866_);
                    lean_dec_ref(v___y_4865_);
                    lean_dec_ref(v___y_4863_);
                    lean_dec_ref(v___y_4862_);
                    lean_dec_ref(v___y_4860_);
                    lean_dec_ref(v___y_4859_);
                    lean_dec_ref(v___y_4858_);
                    v___x_4868_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrProof___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkEqCongrProof___closed__4_once),
                        _init_l_Lean_Meta_Grind_mkEqCongrProof___closed__4,
                    );
                    v___x_4869_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_4868_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v___y_4864_, v_a_4829_);
                    lean_dec_ref(v___y_4864_);
                    return v___x_4869_;
                } else {
                    v___x_4870_ = l_Lean_Expr_constLevels_x21(v___y_4863_);
                    lean_dec_ref(v___y_4863_);
                    v___x_4871_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___y_4859_,
                            v___y_4865_,
                        );
                    if v___x_4871_ == 0 {
                        lean_inc_ref(v___y_4858_);
                        lean_inc_ref(v___y_4862_);
                        v___x_4872_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4862_, v___y_4858_, v___y_4861_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v___y_4864_, v_a_4829_);
                        if lean_obj_tag(v___x_4872_) == 0 {
                            v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
                            lean_inc(v_a_4873_);
                            lean_dec_ref_known(v___x_4872_, 1);
                            lean_inc_ref(v___y_4866_);
                            lean_inc_ref(v___y_4860_);
                            v___x_4874_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4860_, v___y_4866_, v___y_4861_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v___y_4864_, v_a_4829_);
                            lean_dec_ref(v___y_4864_);
                            if lean_obj_tag(v___x_4874_) == 0 {
                                v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
                                v_isSharedCheck_4885_ = (!lean_is_exclusive(v___x_4874_)) as u8;
                                if v_isSharedCheck_4885_ == 0 {
                                    v___x_4877_ = v___x_4874_;
                                    v_isShared_4878_ = v_isSharedCheck_4885_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4875_);
                                    lean_dec(v___x_4874_);
                                    v___x_4877_ = lean_box(0);
                                    v_isShared_4878_ = v_isSharedCheck_4885_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4873_);
                                lean_dec(v___x_4870_);
                                lean_dec_ref(v___y_4866_);
                                lean_dec_ref(v___y_4865_);
                                lean_dec_ref(v___y_4862_);
                                lean_dec_ref(v___y_4860_);
                                lean_dec_ref(v___y_4859_);
                                lean_dec_ref(v___y_4858_);
                                return v___x_4874_;
                            }
                        } else {
                            lean_dec(v___x_4870_);
                            lean_dec_ref(v___y_4866_);
                            lean_dec_ref(v___y_4865_);
                            lean_dec_ref(v___y_4864_);
                            lean_dec_ref(v___y_4862_);
                            lean_dec_ref(v___y_4860_);
                            lean_dec_ref(v___y_4859_);
                            lean_dec_ref(v___y_4858_);
                            return v___x_4872_;
                        }
                    } else {
                        lean_dec_ref(v___y_4865_);
                        v___x_4886_ = 0;
                        lean_inc_ref(v___y_4858_);
                        lean_inc_ref(v___y_4862_);
                        v___x_4887_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4862_, v___y_4858_, v___x_4886_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v___y_4864_, v_a_4829_);
                        if lean_obj_tag(v___x_4887_) == 0 {
                            v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
                            lean_inc(v_a_4888_);
                            lean_dec_ref_known(v___x_4887_, 1);
                            lean_inc_ref(v___y_4866_);
                            lean_inc_ref(v___y_4860_);
                            v___x_4889_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v___y_4860_, v___y_4866_, v___x_4886_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v___y_4864_, v_a_4829_);
                            lean_dec_ref(v___y_4864_);
                            if lean_obj_tag(v___x_4889_) == 0 {
                                v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
                                v_isSharedCheck_4900_ = (!lean_is_exclusive(v___x_4889_)) as u8;
                                if v_isSharedCheck_4900_ == 0 {
                                    v___x_4892_ = v___x_4889_;
                                    v_isShared_4893_ = v_isSharedCheck_4900_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4890_);
                                    lean_dec(v___x_4889_);
                                    v___x_4892_ = lean_box(0);
                                    v_isShared_4893_ = v_isSharedCheck_4900_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4888_);
                                lean_dec(v___x_4870_);
                                lean_dec_ref(v___y_4866_);
                                lean_dec_ref(v___y_4862_);
                                lean_dec_ref(v___y_4860_);
                                lean_dec_ref(v___y_4859_);
                                lean_dec_ref(v___y_4858_);
                                return v___x_4889_;
                            }
                        } else {
                            lean_dec(v___x_4870_);
                            lean_dec_ref(v___y_4866_);
                            lean_dec_ref(v___y_4864_);
                            lean_dec_ref(v___y_4862_);
                            lean_dec_ref(v___y_4860_);
                            lean_dec_ref(v___y_4859_);
                            lean_dec_ref(v___y_4858_);
                            return v___x_4887_;
                        }
                    }
                }
            }
            4 => {
                v___x_4879_ = l_Lean_Meta_Grind_mkEqCongrProof___closed__6;
                v___x_4880_ = l_Lean_mkConst(v___x_4879_, v___x_4870_);
                v___x_4881_ = l_Lean_mkApp8(
                    v___x_4880_,
                    v___y_4859_,
                    v___y_4865_,
                    v___y_4862_,
                    v___y_4860_,
                    v___y_4858_,
                    v___y_4866_,
                    v_a_4873_,
                    v_a_4875_,
                );
                if v_isShared_4878_ == 0 {
                    lean_ctor_set(v___x_4877_, 0, v___x_4881_);
                    v___x_4883_ = v___x_4877_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
                    v___x_4883_ = v_reuseFailAlloc_4884_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4883_;
            }
            6 => {
                v___x_4894_ = l_Lean_Meta_Grind_mkEqCongrProof___closed__8;
                v___x_4895_ = l_Lean_mkConst(v___x_4894_, v___x_4870_);
                v___x_4896_ = l_Lean_mkApp7(
                    v___x_4895_,
                    v___y_4859_,
                    v___y_4862_,
                    v___y_4860_,
                    v___y_4858_,
                    v___y_4866_,
                    v_a_4888_,
                    v_a_4890_,
                );
                if v_isShared_4893_ == 0 {
                    lean_ctor_set(v___x_4892_, 0, v___x_4896_);
                    v___x_4898_ = v___x_4892_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4896_);
                    v___x_4898_ = v_reuseFailAlloc_4899_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4898_;
            }
            8 => {
                v___x_4920_ = lean_unsigned_to_nat(1);
                v___x_4921_ = lean_nat_add(v_currRecDepth_4904_, v___x_4920_);
                lean_inc_ref(v_inheritedTraceOptions_4916_);
                lean_inc(v_cancelTk_x3f_4914_);
                lean_inc(v_currMacroScope_4912_);
                lean_inc(v_quotContext_4911_);
                lean_inc(v_maxHeartbeats_4910_);
                lean_inc(v_initHeartbeats_4909_);
                lean_inc(v_openDecls_4908_);
                lean_inc(v_currNamespace_4907_);
                lean_inc(v_ref_4906_);
                lean_inc(v_maxRecDepth_4905_);
                lean_inc_ref(v_options_4903_);
                lean_inc_ref(v_fileMap_4902_);
                lean_inc_ref(v_fileName_4901_);
                v___x_4922_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4922_, 0, v_fileName_4901_);
                lean_ctor_set(v___x_4922_, 1, v_fileMap_4902_);
                lean_ctor_set(v___x_4922_, 2, v_options_4903_);
                lean_ctor_set(v___x_4922_, 3, v___x_4921_);
                lean_ctor_set(v___x_4922_, 4, v_maxRecDepth_4905_);
                lean_ctor_set(v___x_4922_, 5, v_ref_4906_);
                lean_ctor_set(v___x_4922_, 6, v_currNamespace_4907_);
                lean_ctor_set(v___x_4922_, 7, v_openDecls_4908_);
                lean_ctor_set(v___x_4922_, 8, v_initHeartbeats_4909_);
                lean_ctor_set(v___x_4922_, 9, v_maxHeartbeats_4910_);
                lean_ctor_set(v___x_4922_, 10, v_quotContext_4911_);
                lean_ctor_set(v___x_4922_, 11, v_currMacroScope_4912_);
                lean_ctor_set(v___x_4922_, 12, v_cancelTk_x3f_4914_);
                lean_ctor_set(v___x_4922_, 13, v_inheritedTraceOptions_4916_);
                lean_ctor_set_uint8(
                    v___x_4922_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4913_,
                );
                lean_ctor_set_uint8(
                    v___x_4922_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4915_,
                );
                if v___x_4918_ == 0 {
                    lean_dec_ref(v___x_4917_);
                    lean_dec_ref(v_rhs_4819_);
                    v___y_4832_ = v_a_4820_;
                    v___y_4833_ = v_a_4821_;
                    v___y_4834_ = v_a_4822_;
                    v___y_4835_ = v_a_4823_;
                    v___y_4836_ = v_a_4824_;
                    v___y_4837_ = v_a_4825_;
                    v___y_4838_ = v_a_4826_;
                    v___y_4839_ = v_a_4827_;
                    v___y_4840_ = v___x_4922_;
                    v___y_4841_ = v_a_4829_;
                    state = 1;
                    continue;
                } else {
                    v_arg_4923_ = lean_ctor_get(v___x_4917_, 1);
                    lean_inc_ref(v_arg_4923_);
                    v___x_4924_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4917_);
                    v___x_4925_ = l_Lean_Expr_isApp(v___x_4924_);
                    if v___x_4925_ == 0 {
                        lean_dec_ref(v___x_4924_);
                        lean_dec_ref(v_arg_4923_);
                        lean_dec_ref(v_rhs_4819_);
                        v___y_4832_ = v_a_4820_;
                        v___y_4833_ = v_a_4821_;
                        v___y_4834_ = v_a_4822_;
                        v___y_4835_ = v_a_4823_;
                        v___y_4836_ = v_a_4824_;
                        v___y_4837_ = v_a_4825_;
                        v___y_4838_ = v_a_4826_;
                        v___y_4839_ = v_a_4827_;
                        v___y_4840_ = v___x_4922_;
                        v___y_4841_ = v_a_4829_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_4926_ = lean_ctor_get(v___x_4924_, 1);
                        lean_inc_ref(v_arg_4926_);
                        v___x_4927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4924_);
                        v___x_4928_ = l_Lean_Expr_isApp(v___x_4927_);
                        if v___x_4928_ == 0 {
                            lean_dec_ref(v___x_4927_);
                            lean_dec_ref(v_arg_4926_);
                            lean_dec_ref(v_arg_4923_);
                            lean_dec_ref(v_rhs_4819_);
                            v___y_4832_ = v_a_4820_;
                            v___y_4833_ = v_a_4821_;
                            v___y_4834_ = v_a_4822_;
                            v___y_4835_ = v_a_4823_;
                            v___y_4836_ = v_a_4824_;
                            v___y_4837_ = v_a_4825_;
                            v___y_4838_ = v_a_4826_;
                            v___y_4839_ = v_a_4827_;
                            v___y_4840_ = v___x_4922_;
                            v___y_4841_ = v_a_4829_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_4929_ = lean_ctor_get(v___x_4927_, 1);
                            lean_inc_ref(v_arg_4929_);
                            v___x_4930_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4927_);
                            v___x_4931_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1;
                            v___x_4932_ = l_Lean_Expr_isConstOf(v___x_4930_, v___x_4931_);
                            if v___x_4932_ == 0 {
                                lean_dec_ref(v___x_4930_);
                                lean_dec_ref(v_arg_4929_);
                                lean_dec_ref(v_arg_4926_);
                                lean_dec_ref(v_arg_4923_);
                                lean_dec_ref(v_rhs_4819_);
                                v___y_4832_ = v_a_4820_;
                                v___y_4833_ = v_a_4821_;
                                v___y_4834_ = v_a_4822_;
                                v___y_4835_ = v_a_4823_;
                                v___y_4836_ = v_a_4824_;
                                v___y_4837_ = v_a_4825_;
                                v___y_4838_ = v_a_4826_;
                                v___y_4839_ = v_a_4827_;
                                v___y_4840_ = v___x_4922_;
                                v___y_4841_ = v_a_4829_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4933_ = l_Lean_Expr_cleanupAnnotations(v_rhs_4819_);
                                v___x_4934_ = l_Lean_Expr_isApp(v___x_4933_);
                                if v___x_4934_ == 0 {
                                    lean_dec_ref(v___x_4933_);
                                    lean_dec_ref(v___x_4930_);
                                    lean_dec_ref(v_arg_4929_);
                                    lean_dec_ref(v_arg_4926_);
                                    lean_dec_ref(v_arg_4923_);
                                    v___y_4845_ = v_a_4820_;
                                    v___y_4846_ = v_a_4821_;
                                    v___y_4847_ = v_a_4822_;
                                    v___y_4848_ = v_a_4823_;
                                    v___y_4849_ = v_a_4824_;
                                    v___y_4850_ = v_a_4825_;
                                    v___y_4851_ = v_a_4826_;
                                    v___y_4852_ = v_a_4827_;
                                    v___y_4853_ = v___x_4922_;
                                    v___y_4854_ = v_a_4829_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_4935_ = lean_ctor_get(v___x_4933_, 1);
                                    lean_inc_ref(v_arg_4935_);
                                    v___x_4936_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4933_);
                                    v___x_4937_ = l_Lean_Expr_isApp(v___x_4936_);
                                    if v___x_4937_ == 0 {
                                        lean_dec_ref(v___x_4936_);
                                        lean_dec_ref(v_arg_4935_);
                                        lean_dec_ref(v___x_4930_);
                                        lean_dec_ref(v_arg_4929_);
                                        lean_dec_ref(v_arg_4926_);
                                        lean_dec_ref(v_arg_4923_);
                                        v___y_4845_ = v_a_4820_;
                                        v___y_4846_ = v_a_4821_;
                                        v___y_4847_ = v_a_4822_;
                                        v___y_4848_ = v_a_4823_;
                                        v___y_4849_ = v_a_4824_;
                                        v___y_4850_ = v_a_4825_;
                                        v___y_4851_ = v_a_4826_;
                                        v___y_4852_ = v_a_4827_;
                                        v___y_4853_ = v___x_4922_;
                                        v___y_4854_ = v_a_4829_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_arg_4938_ = lean_ctor_get(v___x_4936_, 1);
                                        lean_inc_ref(v_arg_4938_);
                                        v___x_4939_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4936_);
                                        v___x_4940_ = l_Lean_Expr_isApp(v___x_4939_);
                                        if v___x_4940_ == 0 {
                                            lean_dec_ref(v___x_4939_);
                                            lean_dec_ref(v_arg_4938_);
                                            lean_dec_ref(v_arg_4935_);
                                            lean_dec_ref(v___x_4930_);
                                            lean_dec_ref(v_arg_4929_);
                                            lean_dec_ref(v_arg_4926_);
                                            lean_dec_ref(v_arg_4923_);
                                            v___y_4845_ = v_a_4820_;
                                            v___y_4846_ = v_a_4821_;
                                            v___y_4847_ = v_a_4822_;
                                            v___y_4848_ = v_a_4823_;
                                            v___y_4849_ = v_a_4824_;
                                            v___y_4850_ = v_a_4825_;
                                            v___y_4851_ = v_a_4826_;
                                            v___y_4852_ = v_a_4827_;
                                            v___y_4853_ = v___x_4922_;
                                            v___y_4854_ = v_a_4829_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v_arg_4941_ = lean_ctor_get(v___x_4939_, 1);
                                            lean_inc_ref(v_arg_4941_);
                                            v___x_4942_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_4939_);
                                            v___x_4943_ =
                                                l_Lean_Expr_isConstOf(v___x_4942_, v___x_4931_);
                                            lean_dec_ref(v___x_4942_);
                                            if v___x_4943_ == 0 {
                                                lean_dec_ref(v_arg_4941_);
                                                lean_dec_ref(v_arg_4938_);
                                                lean_dec_ref(v_arg_4935_);
                                                lean_dec_ref(v___x_4930_);
                                                lean_dec_ref(v_arg_4929_);
                                                lean_dec_ref(v_arg_4926_);
                                                lean_dec_ref(v_arg_4923_);
                                                v___y_4845_ = v_a_4820_;
                                                v___y_4846_ = v_a_4821_;
                                                v___y_4847_ = v_a_4822_;
                                                v___y_4848_ = v_a_4823_;
                                                v___y_4849_ = v_a_4824_;
                                                v___y_4850_ = v_a_4825_;
                                                v___y_4851_ = v_a_4826_;
                                                v___y_4852_ = v_a_4827_;
                                                v___y_4853_ = v___x_4922_;
                                                v___y_4854_ = v_a_4829_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_4944_ = lean_st_ref_get(v_a_4820_);
                                                v___x_4945_ = lean_st_ref_get(v_a_4820_);
                                                v___x_4946_ = l_Lean_Meta_Grind_Goal_hasSameRoot(
                                                    v___x_4944_,
                                                    v_arg_4926_,
                                                    v_arg_4938_,
                                                );
                                                lean_dec(v___x_4944_);
                                                if v___x_4946_ == 0 {
                                                    lean_dec(v___x_4945_);
                                                    v___y_4858_ = v_arg_4938_;
                                                    v___y_4859_ = v_arg_4929_;
                                                    v___y_4860_ = v_arg_4923_;
                                                    v___y_4861_ = v___x_4943_;
                                                    v___y_4862_ = v_arg_4926_;
                                                    v___y_4863_ = v___x_4930_;
                                                    v___y_4864_ = v___x_4922_;
                                                    v___y_4865_ = v_arg_4941_;
                                                    v___y_4866_ = v_arg_4935_;
                                                    v___y_4867_ = v___x_4946_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    v___x_4947_ =
                                                        l_Lean_Meta_Grind_Goal_hasSameRoot(
                                                            v___x_4945_,
                                                            v_arg_4923_,
                                                            v_arg_4935_,
                                                        );
                                                    lean_dec(v___x_4945_);
                                                    v___y_4858_ = v_arg_4938_;
                                                    v___y_4859_ = v_arg_4929_;
                                                    v___y_4860_ = v_arg_4923_;
                                                    v___y_4861_ = v___x_4943_;
                                                    v___y_4862_ = v_arg_4926_;
                                                    v___y_4863_ = v___x_4930_;
                                                    v___y_4864_ = v___x_4922_;
                                                    v___y_4865_ = v_arg_4941_;
                                                    v___y_4866_ = v_arg_4935_;
                                                    v___y_4867_ = v___x_4947_;
                                                    state = 3;
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
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4()
-> *mut LeanObject {
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    v___x_4962_ = lean_box(0);
    v___x_4963_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__3;
    v___x_4964_ = l_Lean_mkConst(v___x_4963_, v___x_4962_);
    return v___x_4964_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(
    mut v_lhs_4965_: *mut LeanObject,
    mut v_rhs_4966_: *mut LeanObject,
    mut v_heq_4967_: u8,
    mut v_a_4968_: *mut LeanObject,
    mut v_a_4969_: *mut LeanObject,
    mut v_a_4970_: *mut LeanObject,
    mut v_a_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v_a_4973_: *mut LeanObject,
    mut v_a_4974_: *mut LeanObject,
    mut v_a_4975_: *mut LeanObject,
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    v___x_4979_ = l_Lean_Expr_appFn_x21(v_lhs_4965_);
    v_p_4980_ = l_Lean_Expr_appArg_x21(v___x_4979_);
    lean_dec_ref(v___x_4979_);
    v___x_4981_ = l_Lean_Expr_appFn_x21(v_rhs_4966_);
    v_q_4982_ = l_Lean_Expr_appArg_x21(v___x_4981_);
    lean_dec_ref(v___x_4981_);
    v___x_4983_ = 0;
    lean_inc_ref(v_q_4982_);
    lean_inc_ref(v_p_4980_);
    v___x_4984_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
        v_p_4980_,
        v_q_4982_,
        v___x_4983_,
        v_a_4968_,
        v_a_4969_,
        v_a_4970_,
        v_a_4971_,
        v_a_4972_,
        v_a_4973_,
        v_a_4974_,
        v_a_4975_,
        v_a_4976_,
        v_a_4977_,
    );
    if lean_obj_tag(v___x_4984_) == 0 {
        let mut v_a_4985_: *mut LeanObject = core::ptr::null_mut();
        let mut v_hp_4986_: *mut LeanObject = core::ptr::null_mut();
        let mut v_hq_4987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
        v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
        lean_inc(v_a_4985_);
        lean_dec_ref_known(v___x_4984_, 1);
        v_hp_4986_ = l_Lean_Expr_appArg_x21(v_lhs_4965_);
        v_hq_4987_ = l_Lean_Expr_appArg_x21(v_rhs_4966_);
        v___x_4988_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___closed__4);
        v___x_4989_ = l_Lean_mkApp5(
            v___x_4988_,
            v_p_4980_,
            v_q_4982_,
            v_a_4985_,
            v_hp_4986_,
            v_hq_4987_,
        );
        v___x_4990_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(
            v___x_4989_,
            v_heq_4967_,
            v_a_4974_,
            v_a_4975_,
            v_a_4976_,
            v_a_4977_,
        );
        return v___x_4990_;
    } else {
        lean_dec_ref(v_q_4982_);
        lean_dec_ref(v_p_4980_);
        return v___x_4984_;
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2()
-> *mut LeanObject {
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    v___x_5001_ = lean_box(0);
    v___x_5002_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__1;
    v___x_5003_ = l_Lean_mkConst(v___x_5002_, v___x_5001_);
    return v___x_5003_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(
    mut v_lhs_5004_: *mut LeanObject,
    mut v_rhs_5005_: *mut LeanObject,
    mut v_heq_5006_: u8,
    mut v_a_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
    mut v_a_5010_: *mut LeanObject,
    mut v_a_5011_: *mut LeanObject,
    mut v_a_5012_: *mut LeanObject,
    mut v_a_5013_: *mut LeanObject,
    mut v_a_5014_: *mut LeanObject,
    mut v_a_5015_: *mut LeanObject,
    mut v_a_5016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    v___x_5018_ = l_Lean_Expr_appFn_x21(v_lhs_5004_);
    v_p_5019_ = l_Lean_Expr_appArg_x21(v___x_5018_);
    lean_dec_ref(v___x_5018_);
    v___x_5020_ = l_Lean_Expr_appFn_x21(v_rhs_5005_);
    v_q_5021_ = l_Lean_Expr_appArg_x21(v___x_5020_);
    lean_dec_ref(v___x_5020_);
    v___x_5022_ = 0;
    lean_inc_ref(v_q_5021_);
    lean_inc_ref(v_p_5019_);
    v___x_5023_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
        v_p_5019_,
        v_q_5021_,
        v___x_5022_,
        v_a_5007_,
        v_a_5008_,
        v_a_5009_,
        v_a_5010_,
        v_a_5011_,
        v_a_5012_,
        v_a_5013_,
        v_a_5014_,
        v_a_5015_,
        v_a_5016_,
    );
    if lean_obj_tag(v___x_5023_) == 0 {
        let mut v_a_5024_: *mut LeanObject = core::ptr::null_mut();
        let mut v_hp_5025_: *mut LeanObject = core::ptr::null_mut();
        let mut v_hq_5026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
        v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
        lean_inc(v_a_5024_);
        lean_dec_ref_known(v___x_5023_, 1);
        v_hp_5025_ = l_Lean_Expr_appArg_x21(v_lhs_5004_);
        v_hq_5026_ = l_Lean_Expr_appArg_x21(v_rhs_5005_);
        v___x_5027_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___closed__2);
        v___x_5028_ = l_Lean_mkApp5(
            v___x_5027_,
            v_p_5019_,
            v_q_5021_,
            v_a_5024_,
            v_hp_5025_,
            v_hq_5026_,
        );
        v___x_5029_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(
            v___x_5028_,
            v_heq_5006_,
            v_a_5013_,
            v_a_5014_,
            v_a_5015_,
            v_a_5016_,
        );
        return v___x_5029_;
    } else {
        lean_dec_ref(v_q_5021_);
        lean_dec_ref(v_p_5019_);
        return v___x_5023_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(
    mut v_lhs_5030_: *mut LeanObject,
    mut v_rhs_5031_: *mut LeanObject,
    mut v_heq_5032_: u8,
    mut v_a_5033_: *mut LeanObject,
    mut v_a_5034_: *mut LeanObject,
    mut v_a_5035_: *mut LeanObject,
    mut v_a_5036_: *mut LeanObject,
    mut v_a_5037_: *mut LeanObject,
    mut v_a_5038_: *mut LeanObject,
    mut v_a_5039_: *mut LeanObject,
    mut v_a_5040_: *mut LeanObject,
    mut v_a_5041_: *mut LeanObject,
    mut v_a_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderType_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u8 = 0;
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5058_: u8 = 0;
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5068_: u8 = 0;
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5070_: u8 = 0;
    let mut v_ctxApprox_5071_: u8 = 0;
    let mut v_quasiPatternApprox_5072_: u8 = 0;
    let mut v_constApprox_5073_: u8 = 0;
    let mut v_isDefEqStuckEx_5074_: u8 = 0;
    let mut v_unificationHints_5075_: u8 = 0;
    let mut v_proofIrrelevance_5076_: u8 = 0;
    let mut v_assignSyntheticOpaque_5077_: u8 = 0;
    let mut v_offsetCnstrs_5078_: u8 = 0;
    let mut v_etaStruct_5079_: u8 = 0;
    let mut v_univApprox_5080_: u8 = 0;
    let mut v_iota_5081_: u8 = 0;
    let mut v_beta_5082_: u8 = 0;
    let mut v_proj_5083_: u8 = 0;
    let mut v_zeta_5084_: u8 = 0;
    let mut v_zetaDelta_5085_: u8 = 0;
    let mut v_zetaUnused_5086_: u8 = 0;
    let mut v_zetaHave_5087_: u8 = 0;
    let mut v_trackZetaDelta_5088_: u8 = 0;
    let mut v_zetaDeltaSet_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5095_: u8 = 0;
    let mut v_inTypeClassResolution_5096_: u8 = 0;
    let mut v_cacheInferType_5097_: u8 = 0;
    let mut v_a_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5100_: u8 = 0;
    let mut v_ctxApprox_5101_: u8 = 0;
    let mut v_quasiPatternApprox_5102_: u8 = 0;
    let mut v_constApprox_5103_: u8 = 0;
    let mut v_isDefEqStuckEx_5104_: u8 = 0;
    let mut v_unificationHints_5105_: u8 = 0;
    let mut v_proofIrrelevance_5106_: u8 = 0;
    let mut v_assignSyntheticOpaque_5107_: u8 = 0;
    let mut v_offsetCnstrs_5108_: u8 = 0;
    let mut v_etaStruct_5109_: u8 = 0;
    let mut v_univApprox_5110_: u8 = 0;
    let mut v_iota_5111_: u8 = 0;
    let mut v_beta_5112_: u8 = 0;
    let mut v_proj_5113_: u8 = 0;
    let mut v_zeta_5114_: u8 = 0;
    let mut v_zetaDelta_5115_: u8 = 0;
    let mut v_zetaUnused_5116_: u8 = 0;
    let mut v_zetaHave_5117_: u8 = 0;
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5120_: u8 = 0;
    let mut v___x_5121_: u8 = 0;
    let mut v_config_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: u64 = 0;
    let mut v___x_5125_: u64 = 0;
    let mut v___x_5126_: u64 = 0;
    let mut v___x_5127_: u64 = 0;
    let mut v___x_5128_: u64 = 0;
    let mut v_key_5129_: u64 = 0;
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_reuseFailAlloc_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5144_: u8 = 0;
    let mut v___x_5145_: u8 = 0;
    let mut v_config_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u64 = 0;
    let mut v___x_5148_: u64 = 0;
    let mut v___x_5149_: u64 = 0;
    let mut v___x_5150_: u64 = 0;
    let mut v___x_5151_: u64 = 0;
    let mut v_key_5152_: u64 = 0;
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5165_: u8 = 0;
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: u8 = 0;
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: u8 = 0;
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut v___y_5193_: u8 = 0;
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: u8 = 0;
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    let mut v___y_5205_: u8 = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: u8 = 0;
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    let mut v___y_5215_: u8 = 0;
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: u8 = 0;
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_lhs_5030_) == 7 {
                    if lean_obj_tag(v_rhs_5031_) == 7 {
                        v_binderType_5044_ = lean_ctor_get(v_lhs_5030_, 1);
                        lean_inc_ref_n(v_binderType_5044_, 2);
                        v_body_5045_ = lean_ctor_get(v_lhs_5030_, 2);
                        lean_inc_ref(v_body_5045_);
                        lean_dec_ref_known(v_lhs_5030_, 3);
                        v_binderType_5046_ = lean_ctor_get(v_rhs_5031_, 1);
                        lean_inc_ref(v_binderType_5046_);
                        v_body_5047_ = lean_ctor_get(v_rhs_5031_, 2);
                        lean_inc_ref(v_body_5047_);
                        lean_dec_ref_known(v_rhs_5031_, 3);
                        v___x_5069_ = l_Lean_Meta_Context_config(v_a_5039_);
                        v_foApprox_5070_ = lean_ctor_get_uint8(v___x_5069_, 0 as u32);
                        v_ctxApprox_5071_ = lean_ctor_get_uint8(v___x_5069_, 1 as u32);
                        v_quasiPatternApprox_5072_ = lean_ctor_get_uint8(v___x_5069_, 2 as u32);
                        v_constApprox_5073_ = lean_ctor_get_uint8(v___x_5069_, 3 as u32);
                        v_isDefEqStuckEx_5074_ = lean_ctor_get_uint8(v___x_5069_, 4 as u32);
                        v_unificationHints_5075_ = lean_ctor_get_uint8(v___x_5069_, 5 as u32);
                        v_proofIrrelevance_5076_ = lean_ctor_get_uint8(v___x_5069_, 6 as u32);
                        v_assignSyntheticOpaque_5077_ = lean_ctor_get_uint8(v___x_5069_, 7 as u32);
                        v_offsetCnstrs_5078_ = lean_ctor_get_uint8(v___x_5069_, 8 as u32);
                        v_etaStruct_5079_ = lean_ctor_get_uint8(v___x_5069_, 10 as u32);
                        v_univApprox_5080_ = lean_ctor_get_uint8(v___x_5069_, 11 as u32);
                        v_iota_5081_ = lean_ctor_get_uint8(v___x_5069_, 12 as u32);
                        v_beta_5082_ = lean_ctor_get_uint8(v___x_5069_, 13 as u32);
                        v_proj_5083_ = lean_ctor_get_uint8(v___x_5069_, 14 as u32);
                        v_zeta_5084_ = lean_ctor_get_uint8(v___x_5069_, 15 as u32);
                        v_zetaDelta_5085_ = lean_ctor_get_uint8(v___x_5069_, 16 as u32);
                        v_zetaUnused_5086_ = lean_ctor_get_uint8(v___x_5069_, 17 as u32);
                        v_zetaHave_5087_ = lean_ctor_get_uint8(v___x_5069_, 18 as u32);
                        v_trackZetaDelta_5088_ = lean_ctor_get_uint8(
                            v_a_5039_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        );
                        v_zetaDeltaSet_5089_ = lean_ctor_get(v_a_5039_, 1);
                        v_lctx_5090_ = lean_ctor_get(v_a_5039_, 2);
                        v_localInstances_5091_ = lean_ctor_get(v_a_5039_, 3);
                        v_defEqCtx_x3f_5092_ = lean_ctor_get(v_a_5039_, 4);
                        v_synthPendingDepth_5093_ = lean_ctor_get(v_a_5039_, 5);
                        v_canUnfold_x3f_5094_ = lean_ctor_get(v_a_5039_, 6);
                        v_univApprox_5095_ = lean_ctor_get_uint8(
                            v_a_5039_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        );
                        v_inTypeClassResolution_5096_ = lean_ctor_get_uint8(
                            v_a_5039_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        );
                        v_cacheInferType_5097_ = lean_ctor_get_uint8(
                            v_a_5039_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        );
                        v___x_5145_ = 1;
                        v_config_5146_ = lean_alloc_ctor(0, 0, (19) as u32);
                        lean_ctor_set_uint8(v_config_5146_, 0 as u32, v_foApprox_5070_);
                        lean_ctor_set_uint8(v_config_5146_, 1 as u32, v_ctxApprox_5071_);
                        lean_ctor_set_uint8(v_config_5146_, 2 as u32, v_quasiPatternApprox_5072_);
                        lean_ctor_set_uint8(v_config_5146_, 3 as u32, v_constApprox_5073_);
                        lean_ctor_set_uint8(v_config_5146_, 4 as u32, v_isDefEqStuckEx_5074_);
                        lean_ctor_set_uint8(v_config_5146_, 5 as u32, v_unificationHints_5075_);
                        lean_ctor_set_uint8(v_config_5146_, 6 as u32, v_proofIrrelevance_5076_);
                        lean_ctor_set_uint8(
                            v_config_5146_,
                            7 as u32,
                            v_assignSyntheticOpaque_5077_,
                        );
                        lean_ctor_set_uint8(v_config_5146_, 8 as u32, v_offsetCnstrs_5078_);
                        lean_ctor_set_uint8(v_config_5146_, 9 as u32, v___x_5145_);
                        lean_ctor_set_uint8(v_config_5146_, 10 as u32, v_etaStruct_5079_);
                        lean_ctor_set_uint8(v_config_5146_, 11 as u32, v_univApprox_5080_);
                        lean_ctor_set_uint8(v_config_5146_, 12 as u32, v_iota_5081_);
                        lean_ctor_set_uint8(v_config_5146_, 13 as u32, v_beta_5082_);
                        lean_ctor_set_uint8(v_config_5146_, 14 as u32, v_proj_5083_);
                        lean_ctor_set_uint8(v_config_5146_, 15 as u32, v_zeta_5084_);
                        lean_ctor_set_uint8(v_config_5146_, 16 as u32, v_zetaDelta_5085_);
                        lean_ctor_set_uint8(v_config_5146_, 17 as u32, v_zetaUnused_5086_);
                        lean_ctor_set_uint8(v_config_5146_, 18 as u32, v_zetaHave_5087_);
                        v___x_5147_ = l_Lean_Meta_Context_configKey(v_a_5039_);
                        v___x_5148_ = 3u64;
                        v___x_5149_ = lean_uint64_shift_right(v___x_5147_, v___x_5148_);
                        v___x_5150_ = lean_uint64_shift_left(v___x_5149_, v___x_5148_);
                        v___x_5151_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
                        v_key_5152_ = lean_uint64_lor(v___x_5150_, v___x_5151_);
                        v___x_5153_ = lean_alloc_ctor(0, 1, (8) as u32);
                        lean_ctor_set(v___x_5153_, 0, v_config_5146_);
                        lean_ctor_set_uint64(
                            v___x_5153_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_key_5152_,
                        );
                        lean_inc(v_canUnfold_x3f_5094_);
                        lean_inc(v_synthPendingDepth_5093_);
                        lean_inc(v_defEqCtx_x3f_5092_);
                        lean_inc_ref(v_localInstances_5091_);
                        lean_inc_ref(v_lctx_5090_);
                        lean_inc(v_zetaDeltaSet_5089_);
                        v___x_5154_ = lean_alloc_ctor(0, 7, (4) as u32);
                        lean_ctor_set(v___x_5154_, 0, v___x_5153_);
                        lean_ctor_set(v___x_5154_, 1, v_zetaDeltaSet_5089_);
                        lean_ctor_set(v___x_5154_, 2, v_lctx_5090_);
                        lean_ctor_set(v___x_5154_, 3, v_localInstances_5091_);
                        lean_ctor_set(v___x_5154_, 4, v_defEqCtx_x3f_5092_);
                        lean_ctor_set(v___x_5154_, 5, v_synthPendingDepth_5093_);
                        lean_ctor_set(v___x_5154_, 6, v_canUnfold_x3f_5094_);
                        lean_ctor_set_uint8(
                            v___x_5154_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                            v_trackZetaDelta_5088_,
                        );
                        lean_ctor_set_uint8(
                            v___x_5154_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                            v_univApprox_5095_,
                        );
                        lean_ctor_set_uint8(
                            v___x_5154_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                            v_inTypeClassResolution_5096_,
                        );
                        lean_ctor_set_uint8(
                            v___x_5154_,
                            (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                            v_cacheInferType_5097_,
                        );
                        v___x_5155_ = l_Lean_Meta_getLevel(
                            v_binderType_5044_,
                            v___x_5154_,
                            v_a_5040_,
                            v_a_5041_,
                            v_a_5042_,
                        );
                        lean_dec_ref_known(v___x_5154_, 7);
                        if lean_obj_tag(v___x_5155_) == 0 {
                            v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
                            lean_inc(v_a_5156_);
                            lean_dec_ref_known(v___x_5155_, 1);
                            v_a_5099_ = v_a_5156_;
                            state = 4;
                            continue;
                        } else {
                            if lean_obj_tag(v___x_5155_) == 0 {
                                v_a_5157_ = lean_ctor_get(v___x_5155_, 0);
                                lean_inc(v_a_5157_);
                                lean_dec_ref_known(v___x_5155_, 1);
                                v_a_5099_ = v_a_5157_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec_ref(v___x_5069_);
                                lean_dec_ref(v_body_5047_);
                                lean_dec_ref(v_binderType_5046_);
                                lean_dec_ref(v_body_5045_);
                                lean_dec_ref(v_binderType_5044_);
                                v_a_5158_ = lean_ctor_get(v___x_5155_, 0);
                                v_isSharedCheck_5165_ = (!lean_is_exclusive(v___x_5155_)) as u8;
                                if v_isSharedCheck_5165_ == 0 {
                                    v___x_5160_ = v___x_5155_;
                                    v_isShared_5161_ = v_isSharedCheck_5165_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5158_);
                                    lean_dec(v___x_5155_);
                                    v___x_5160_ = lean_box(0);
                                    v_isShared_5161_ = v_isSharedCheck_5165_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_lhs_5030_, 3);
                        lean_dec_ref(v_rhs_5031_);
                        v___x_5166_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__4);
                        v___x_5167_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5166_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                        return v___x_5167_;
                    }
                } else {
                    lean_inc_ref(v_lhs_5030_);
                    v___x_5168_ = l_Lean_Meta_Grind_useFunCC___redArg(
                        v_lhs_5030_,
                        v_a_5033_,
                        v_a_5039_,
                        v_a_5040_,
                        v_a_5041_,
                        v_a_5042_,
                    );
                    if lean_obj_tag(v___x_5168_) == 0 {
                        v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
                        lean_inc(v_a_5169_);
                        lean_dec_ref_known(v___x_5168_, 1);
                        v___x_5170_ = (lean_unbox(v_a_5169_) as u8);
                        lean_dec(v_a_5169_);
                        if v___x_5170_ == 0 {
                            v___x_5171_ = l_Lean_Expr_getAppNumArgs(v_lhs_5030_);
                            v___x_5172_ = l_Lean_Expr_getAppNumArgs(v_rhs_5031_);
                            v___x_5173_ = lean_nat_dec_eq(v___x_5172_, v___x_5171_);
                            lean_dec(v___x_5172_);
                            if v___x_5173_ == 0 {
                                lean_dec(v___x_5171_);
                                lean_dec_ref(v_rhs_5031_);
                                lean_dec_ref(v_lhs_5030_);
                                v___x_5174_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__6);
                                v___x_5175_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5174_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                                return v___x_5175_;
                            } else {
                                v___x_5176_ = l_Lean_Expr_getAppFn(v_lhs_5030_);
                                v___x_5177_ = l_Lean_Expr_getAppFn(v_rhs_5031_);
                                v___x_5209_ = lean_unsigned_to_nat(2);
                                v___x_5210_ = lean_nat_dec_eq(v___x_5171_, v___x_5209_);
                                if v___x_5210_ == 0 {
                                    v___y_5215_ = v___x_5210_;
                                    state = 18;
                                    continue;
                                } else {
                                    v___x_5219_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10;
                                    v___x_5220_ = l_Lean_Expr_isConstOf(v___x_5176_, v___x_5219_);
                                    v___y_5215_ = v___x_5220_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            v___x_5221_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(v_lhs_5030_, v_rhs_5031_, v_heq_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                            return v___x_5221_;
                        }
                    } else {
                        lean_dec_ref(v_rhs_5031_);
                        lean_dec_ref(v_lhs_5030_);
                        v_a_5222_ = lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5229_ = (!lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5229_ == 0 {
                            v___x_5224_ = v___x_5168_;
                            v_isShared_5225_ = v_isSharedCheck_5229_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_5222_);
                            lean_dec(v___x_5168_);
                            v___x_5224_ = lean_box(0);
                            v_isShared_5225_ = v_isSharedCheck_5229_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5051_ = 0;
                lean_inc_ref(v_binderType_5046_);
                lean_inc_ref(v_binderType_5044_);
                v___x_5052_ =
                    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
                        v_binderType_5044_,
                        v_binderType_5046_,
                        v___x_5051_,
                        v_a_5033_,
                        v_a_5034_,
                        v_a_5035_,
                        v_a_5036_,
                        v_a_5037_,
                        v_a_5038_,
                        v_a_5039_,
                        v_a_5040_,
                        v_a_5041_,
                        v_a_5042_,
                    );
                if lean_obj_tag(v___x_5052_) == 0 {
                    v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
                    lean_inc(v_a_5053_);
                    lean_dec_ref_known(v___x_5052_, 1);
                    lean_inc_ref(v_body_5047_);
                    lean_inc_ref(v_body_5045_);
                    v___x_5054_ =
                        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
                            v_body_5045_,
                            v_body_5047_,
                            v___x_5051_,
                            v_a_5033_,
                            v_a_5034_,
                            v_a_5035_,
                            v_a_5036_,
                            v_a_5037_,
                            v_a_5038_,
                            v_a_5039_,
                            v_a_5040_,
                            v_a_5041_,
                            v_a_5042_,
                        );
                    if lean_obj_tag(v___x_5054_) == 0 {
                        v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5068_ = (!lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5068_ == 0 {
                            v___x_5057_ = v___x_5054_;
                            v_isShared_5058_ = v_isSharedCheck_5068_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5055_);
                            lean_dec(v___x_5054_);
                            v___x_5057_ = lean_box(0);
                            v_isShared_5058_ = v_isSharedCheck_5068_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5053_);
                        lean_dec(v_a_5050_);
                        lean_dec(v___y_5049_);
                        lean_dec_ref(v_body_5047_);
                        lean_dec_ref(v_binderType_5046_);
                        lean_dec_ref(v_body_5045_);
                        lean_dec_ref(v_binderType_5044_);
                        return v___x_5054_;
                    }
                } else {
                    lean_dec(v_a_5050_);
                    lean_dec(v___y_5049_);
                    lean_dec_ref(v_body_5047_);
                    lean_dec_ref(v_binderType_5046_);
                    lean_dec_ref(v_body_5045_);
                    lean_dec_ref(v_binderType_5044_);
                    return v___x_5052_;
                }
            }
            2 => {
                v___x_5059_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__1;
                v___x_5060_ = lean_box(0);
                v___x_5061_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5061_, 0, v_a_5050_);
                lean_ctor_set(v___x_5061_, 1, v___x_5060_);
                v___x_5062_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5062_, 0, v___y_5049_);
                lean_ctor_set(v___x_5062_, 1, v___x_5061_);
                v___x_5063_ = l_Lean_mkConst(v___x_5059_, v___x_5062_);
                v___x_5064_ = l_Lean_mkApp6(
                    v___x_5063_,
                    v_binderType_5044_,
                    v_binderType_5046_,
                    v_body_5045_,
                    v_body_5047_,
                    v_a_5053_,
                    v_a_5055_,
                );
                if v_isShared_5058_ == 0 {
                    lean_ctor_set(v___x_5057_, 0, v___x_5064_);
                    v___x_5066_ = v___x_5057_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5064_);
                    v___x_5066_ = v_reuseFailAlloc_5067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5066_;
            }
            4 => {
                v_foApprox_5100_ = lean_ctor_get_uint8(v___x_5069_, 0 as u32);
                v_ctxApprox_5101_ = lean_ctor_get_uint8(v___x_5069_, 1 as u32);
                v_quasiPatternApprox_5102_ = lean_ctor_get_uint8(v___x_5069_, 2 as u32);
                v_constApprox_5103_ = lean_ctor_get_uint8(v___x_5069_, 3 as u32);
                v_isDefEqStuckEx_5104_ = lean_ctor_get_uint8(v___x_5069_, 4 as u32);
                v_unificationHints_5105_ = lean_ctor_get_uint8(v___x_5069_, 5 as u32);
                v_proofIrrelevance_5106_ = lean_ctor_get_uint8(v___x_5069_, 6 as u32);
                v_assignSyntheticOpaque_5107_ = lean_ctor_get_uint8(v___x_5069_, 7 as u32);
                v_offsetCnstrs_5108_ = lean_ctor_get_uint8(v___x_5069_, 8 as u32);
                v_etaStruct_5109_ = lean_ctor_get_uint8(v___x_5069_, 10 as u32);
                v_univApprox_5110_ = lean_ctor_get_uint8(v___x_5069_, 11 as u32);
                v_iota_5111_ = lean_ctor_get_uint8(v___x_5069_, 12 as u32);
                v_beta_5112_ = lean_ctor_get_uint8(v___x_5069_, 13 as u32);
                v_proj_5113_ = lean_ctor_get_uint8(v___x_5069_, 14 as u32);
                v_zeta_5114_ = lean_ctor_get_uint8(v___x_5069_, 15 as u32);
                v_zetaDelta_5115_ = lean_ctor_get_uint8(v___x_5069_, 16 as u32);
                v_zetaUnused_5116_ = lean_ctor_get_uint8(v___x_5069_, 17 as u32);
                v_zetaHave_5117_ = lean_ctor_get_uint8(v___x_5069_, 18 as u32);
                v_isSharedCheck_5144_ = (!lean_is_exclusive(v___x_5069_)) as u8;
                if v_isSharedCheck_5144_ == 0 {
                    v___x_5119_ = v___x_5069_;
                    v_isShared_5120_ = v_isSharedCheck_5144_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_5069_);
                    v___x_5119_ = lean_box(0);
                    v_isShared_5120_ = v_isSharedCheck_5144_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5121_ = 1;
                if v_isShared_5120_ == 0 {
                    v_config_5123_ = v___x_5119_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 0 as u32, v_foApprox_5100_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 1 as u32, v_ctxApprox_5101_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5143_,
                        2 as u32,
                        v_quasiPatternApprox_5102_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 3 as u32, v_constApprox_5103_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 4 as u32, v_isDefEqStuckEx_5104_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 5 as u32, v_unificationHints_5105_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 6 as u32, v_proofIrrelevance_5106_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5143_,
                        7 as u32,
                        v_assignSyntheticOpaque_5107_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 8 as u32, v_offsetCnstrs_5108_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 10 as u32, v_etaStruct_5109_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 11 as u32, v_univApprox_5110_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 12 as u32, v_iota_5111_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 13 as u32, v_beta_5112_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 14 as u32, v_proj_5113_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 15 as u32, v_zeta_5114_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 16 as u32, v_zetaDelta_5115_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 17 as u32, v_zetaUnused_5116_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5143_, 18 as u32, v_zetaHave_5117_);
                    v_config_5123_ = v_reuseFailAlloc_5143_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_ctor_set_uint8(v_config_5123_, 9 as u32, v___x_5121_);
                v___x_5124_ = l_Lean_Meta_Context_configKey(v_a_5039_);
                v___x_5125_ = 3u64;
                v___x_5126_ = lean_uint64_shift_right(v___x_5124_, v___x_5125_);
                v___x_5127_ = lean_uint64_shift_left(v___x_5126_, v___x_5125_);
                v___x_5128_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__2);
                v_key_5129_ = lean_uint64_lor(v___x_5127_, v___x_5128_);
                v___x_5130_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5130_, 0, v_config_5123_);
                lean_ctor_set_uint64(
                    v___x_5130_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_5129_,
                );
                lean_inc(v_canUnfold_x3f_5094_);
                lean_inc(v_synthPendingDepth_5093_);
                lean_inc(v_defEqCtx_x3f_5092_);
                lean_inc_ref(v_localInstances_5091_);
                lean_inc_ref(v_lctx_5090_);
                lean_inc(v_zetaDeltaSet_5089_);
                v___x_5131_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5131_, 0, v___x_5130_);
                lean_ctor_set(v___x_5131_, 1, v_zetaDeltaSet_5089_);
                lean_ctor_set(v___x_5131_, 2, v_lctx_5090_);
                lean_ctor_set(v___x_5131_, 3, v_localInstances_5091_);
                lean_ctor_set(v___x_5131_, 4, v_defEqCtx_x3f_5092_);
                lean_ctor_set(v___x_5131_, 5, v_synthPendingDepth_5093_);
                lean_ctor_set(v___x_5131_, 6, v_canUnfold_x3f_5094_);
                lean_ctor_set_uint8(
                    v___x_5131_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5088_,
                );
                lean_ctor_set_uint8(
                    v___x_5131_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5095_,
                );
                lean_ctor_set_uint8(
                    v___x_5131_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5096_,
                );
                lean_ctor_set_uint8(
                    v___x_5131_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5097_,
                );
                lean_inc_ref(v_body_5045_);
                v___x_5132_ = l_Lean_Meta_getLevel(
                    v_body_5045_,
                    v___x_5131_,
                    v_a_5040_,
                    v_a_5041_,
                    v_a_5042_,
                );
                lean_dec_ref_known(v___x_5131_, 7);
                if lean_obj_tag(v___x_5132_) == 0 {
                    v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
                    lean_inc(v_a_5133_);
                    lean_dec_ref_known(v___x_5132_, 1);
                    v___y_5049_ = v_a_5099_;
                    v_a_5050_ = v_a_5133_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___x_5132_) == 0 {
                        v_a_5134_ = lean_ctor_get(v___x_5132_, 0);
                        lean_inc(v_a_5134_);
                        lean_dec_ref_known(v___x_5132_, 1);
                        v___y_5049_ = v_a_5099_;
                        v_a_5050_ = v_a_5134_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_5099_);
                        lean_dec_ref(v_body_5047_);
                        lean_dec_ref(v_binderType_5046_);
                        lean_dec_ref(v_body_5045_);
                        lean_dec_ref(v_binderType_5044_);
                        v_a_5135_ = lean_ctor_get(v___x_5132_, 0);
                        v_isSharedCheck_5142_ = (!lean_is_exclusive(v___x_5132_)) as u8;
                        if v_isSharedCheck_5142_ == 0 {
                            v___x_5137_ = v___x_5132_;
                            v_isShared_5138_ = v_isSharedCheck_5142_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5135_);
                            lean_dec(v___x_5132_);
                            v___x_5137_ = lean_box(0);
                            v_isShared_5138_ = v_isSharedCheck_5142_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_5138_ == 0 {
                    v___x_5140_ = v___x_5137_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
                    v___x_5140_ = v_reuseFailAlloc_5141_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5140_;
            }
            9 => {
                if v_isShared_5161_ == 0 {
                    v___x_5163_ = v___x_5160_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_a_5158_);
                    v___x_5163_ = v_reuseFailAlloc_5164_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5163_;
            }
            11 => {
                lean_inc_ref(v_rhs_5031_);
                lean_inc_ref(v_lhs_5030_);
                v___x_5179_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isCongrDefaultProofTarget(v_lhs_5030_, v_rhs_5031_, v___x_5176_, v___x_5177_, v___x_5171_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                lean_dec_ref(v___x_5177_);
                if lean_obj_tag(v___x_5179_) == 0 {
                    v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
                    lean_inc(v_a_5180_);
                    lean_dec_ref_known(v___x_5179_, 1);
                    v___x_5181_ = (lean_unbox(v_a_5180_) as u8);
                    lean_dec(v_a_5180_);
                    if v___x_5181_ == 0 {
                        v___x_5182_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(v_lhs_5030_, v_rhs_5031_, v_heq_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                        return v___x_5182_;
                    } else {
                        v___x_5183_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(v_lhs_5030_, v_rhs_5031_, v_heq_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                        lean_dec_ref(v_rhs_5031_);
                        lean_dec_ref(v_lhs_5030_);
                        return v___x_5183_;
                    }
                } else {
                    lean_dec_ref(v_rhs_5031_);
                    lean_dec_ref(v_lhs_5030_);
                    v_a_5184_ = lean_ctor_get(v___x_5179_, 0);
                    v_isSharedCheck_5191_ = (!lean_is_exclusive(v___x_5179_)) as u8;
                    if v_isSharedCheck_5191_ == 0 {
                        v___x_5186_ = v___x_5179_;
                        v_isShared_5187_ = v_isSharedCheck_5191_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5184_);
                        lean_dec(v___x_5179_);
                        v___x_5186_ = lean_box(0);
                        v_isShared_5187_ = v_isSharedCheck_5191_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_5187_ == 0 {
                    v___x_5189_ = v___x_5186_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5189_;
            }
            14 => {
                if v___y_5193_ == 0 {
                    state = 11;
                    continue;
                } else {
                    v___x_5194_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1;
                    v___x_5195_ = l_Lean_Expr_isConstOf(v___x_5177_, v___x_5194_);
                    if v___x_5195_ == 0 {
                        state = 11;
                        continue;
                    } else {
                        lean_dec_ref(v___x_5177_);
                        lean_dec_ref(v___x_5176_);
                        lean_dec(v___x_5171_);
                        v___x_5196_ = l_Lean_Meta_Grind_mkEqCongrProof(
                            v_lhs_5030_,
                            v_rhs_5031_,
                            v_a_5033_,
                            v_a_5034_,
                            v_a_5035_,
                            v_a_5036_,
                            v_a_5037_,
                            v_a_5038_,
                            v_a_5039_,
                            v_a_5040_,
                            v_a_5041_,
                            v_a_5042_,
                        );
                        if lean_obj_tag(v___x_5196_) == 0 {
                            if v_heq_5032_ == 0 {
                                return v___x_5196_;
                            } else {
                                v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
                                lean_inc(v_a_5197_);
                                lean_dec_ref_known(v___x_5196_, 1);
                                v___x_5198_ = l_Lean_Meta_mkHEqOfEq(
                                    v_a_5197_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_,
                                );
                                return v___x_5198_;
                            }
                        } else {
                            return v___x_5196_;
                        }
                    }
                }
            }
            15 => {
                v___x_5200_ = lean_unsigned_to_nat(3);
                v___x_5201_ = lean_nat_dec_eq(v___x_5171_, v___x_5200_);
                if v___x_5201_ == 0 {
                    v___y_5193_ = v___x_5201_;
                    state = 14;
                    continue;
                } else {
                    v___x_5202_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_isEqProof___closed__1;
                    v___x_5203_ = l_Lean_Expr_isConstOf(v___x_5176_, v___x_5202_);
                    v___y_5193_ = v___x_5203_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                if v___y_5205_ == 0 {
                    state = 15;
                    continue;
                } else {
                    v___x_5206_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8;
                    v___x_5207_ = l_Lean_Expr_isConstOf(v___x_5177_, v___x_5206_);
                    if v___x_5207_ == 0 {
                        state = 15;
                        continue;
                    } else {
                        lean_dec_ref(v___x_5177_);
                        lean_dec_ref(v___x_5176_);
                        lean_dec(v___x_5171_);
                        v___x_5208_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(v_lhs_5030_, v_rhs_5031_, v_heq_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                        lean_dec_ref(v_rhs_5031_);
                        lean_dec_ref(v_lhs_5030_);
                        return v___x_5208_;
                    }
                }
            }
            17 => {
                if v___x_5210_ == 0 {
                    v___y_5205_ = v___x_5210_;
                    state = 16;
                    continue;
                } else {
                    v___x_5212_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__8;
                    v___x_5213_ = l_Lean_Expr_isConstOf(v___x_5176_, v___x_5212_);
                    v___y_5205_ = v___x_5213_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                if v___y_5215_ == 0 {
                    state = 17;
                    continue;
                } else {
                    v___x_5216_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___closed__10;
                    v___x_5217_ = l_Lean_Expr_isConstOf(v___x_5177_, v___x_5216_);
                    if v___x_5217_ == 0 {
                        state = 17;
                        continue;
                    } else {
                        lean_dec_ref(v___x_5177_);
                        lean_dec_ref(v___x_5176_);
                        lean_dec(v___x_5171_);
                        v___x_5218_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(v_lhs_5030_, v_rhs_5031_, v_heq_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
                        lean_dec_ref(v_rhs_5031_);
                        lean_dec_ref(v_lhs_5030_);
                        return v___x_5218_;
                    }
                }
            }
            19 => {
                if v_isShared_5225_ == 0 {
                    v___x_5227_ = v___x_5224_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(
    mut v_lhs_5230_: *mut LeanObject,
    mut v_rhs_5231_: *mut LeanObject,
    mut v_h_5232_: *mut LeanObject,
    mut v_flipped_5233_: u8,
    mut v_heq_5234_: u8,
    mut v_a_5235_: *mut LeanObject,
    mut v_a_5236_: *mut LeanObject,
    mut v_a_5237_: *mut LeanObject,
    mut v_a_5238_: *mut LeanObject,
    mut v_a_5239_: *mut LeanObject,
    mut v_a_5240_: *mut LeanObject,
    mut v_a_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
    mut v_a_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: u8 = 0;
    v___x_5246_ = l_Lean_Meta_Grind_congrPlaceholderProof;
    v___x_5247_ = lean_expr_eqv(v_h_5232_, v___x_5246_);
    if v___x_5247_ == 0 {
        let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5249_: u8 = 0;
        v___x_5248_ = l_Lean_Meta_Grind_eqCongrSymmPlaceholderProof;
        v___x_5249_ = lean_expr_eqv(v_h_5232_, v___x_5248_);
        if v___x_5249_ == 0 {
            let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_rhs_5231_);
            lean_dec_ref(v_lhs_5230_);
            v___x_5250_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_flipProof(
                v_h_5232_,
                v_flipped_5233_,
                v_heq_5234_,
                v_a_5241_,
                v_a_5242_,
                v_a_5243_,
                v_a_5244_,
            );
            return v___x_5250_;
        } else {
            let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_h_5232_);
            v___x_5251_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(
                v_lhs_5230_,
                v_rhs_5231_,
                v_a_5235_,
                v_a_5236_,
                v_a_5237_,
                v_a_5238_,
                v_a_5239_,
                v_a_5240_,
                v_a_5241_,
                v_a_5242_,
                v_a_5243_,
                v_a_5244_,
            );
            if lean_obj_tag(v___x_5251_) == 0 {
                if v_heq_5234_ == 0 {
                    return v___x_5251_;
                } else {
                    let mut v_a_5252_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
                    v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
                    lean_inc(v_a_5252_);
                    lean_dec_ref_known(v___x_5251_, 1);
                    v___x_5253_ = l_Lean_Meta_mkHEqOfEq(
                        v_a_5252_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_,
                    );
                    return v___x_5253_;
                }
            } else {
                return v___x_5251_;
            }
        }
    } else {
        let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_h_5232_);
        v___x_5254_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(
            v_lhs_5230_,
            v_rhs_5231_,
            v_heq_5234_,
            v_a_5235_,
            v_a_5236_,
            v_a_5237_,
            v_a_5238_,
            v_a_5239_,
            v_a_5240_,
            v_a_5241_,
            v_a_5242_,
            v_a_5243_,
            v_a_5244_,
        );
        return v___x_5254_;
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1()
-> *mut LeanObject {
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    v___x_5256_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5257_ = lean_unsigned_to_nat(29);
    v___x_5258_ = lean_unsigned_to_nat(288);
    v___x_5259_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0;
    v___x_5260_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5261_ = l_mkPanicMessageWithDecl(
        v___x_5260_,
        v___x_5259_,
        v___x_5258_,
        v___x_5257_,
        v___x_5256_,
    );
    return v___x_5261_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2()
-> *mut LeanObject {
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    v___x_5262_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5263_ = lean_unsigned_to_nat(35);
    v___x_5264_ = lean_unsigned_to_nat(287);
    v___x_5265_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__0;
    v___x_5266_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5267_ = l_mkPanicMessageWithDecl(
        v___x_5266_,
        v___x_5265_,
        v___x_5264_,
        v___x_5263_,
        v___x_5262_,
    );
    return v___x_5267_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(
    mut v_lhs_5268_: *mut LeanObject,
    mut v_common_5269_: *mut LeanObject,
    mut v_acc_5270_: *mut LeanObject,
    mut v_heq_5271_: u8,
    mut v_a_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_a_5275_: *mut LeanObject,
    mut v_a_5276_: *mut LeanObject,
    mut v_a_5277_: *mut LeanObject,
    mut v_a_5278_: *mut LeanObject,
    mut v_a_5279_: *mut LeanObject,
    mut v_a_5280_: *mut LeanObject,
    mut v_a_5281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_x3f_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_flipped_5289_: u8 = 0;
    let mut v_val_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5310_: u8 = 0;
    let mut v_a_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut v_isSharedCheck_5319_: u8 = 0;
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5331_: u8 = 0;
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5283_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_lhs_5268_,
                        v_common_5269_,
                    );
                if v___x_5283_ == 0 {
                    v___x_5284_ = lean_st_ref_get(v_a_5272_);
                    lean_inc_ref(v_lhs_5268_);
                    v___x_5285_ = l_Lean_Meta_Grind_Goal_getENode(
                        v___x_5284_,
                        v_lhs_5268_,
                        v_a_5278_,
                        v_a_5279_,
                        v_a_5280_,
                        v_a_5281_,
                    );
                    lean_dec(v___x_5284_);
                    if lean_obj_tag(v___x_5285_) == 0 {
                        v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
                        lean_inc(v_a_5286_);
                        lean_dec_ref_known(v___x_5285_, 1);
                        v_target_x3f_5287_ = lean_ctor_get(v_a_5286_, 4);
                        lean_inc(v_target_x3f_5287_);
                        if lean_obj_tag(v_target_x3f_5287_) == 1 {
                            v_proof_x3f_5288_ = lean_ctor_get(v_a_5286_, 5);
                            lean_inc(v_proof_x3f_5288_);
                            if lean_obj_tag(v_proof_x3f_5288_) == 1 {
                                v_flipped_5289_ = lean_ctor_get_uint8(
                                    v_a_5286_,
                                    (core::mem::size_of::<*mut LeanObject>() * 12) as u32,
                                );
                                lean_dec(v_a_5286_);
                                v_val_5290_ = lean_ctor_get(v_target_x3f_5287_, 0);
                                lean_inc(v_val_5290_);
                                lean_dec_ref_known(v_target_x3f_5287_, 1);
                                v_val_5291_ = lean_ctor_get(v_proof_x3f_5288_, 0);
                                v_isSharedCheck_5319_ =
                                    (!lean_is_exclusive(v_proof_x3f_5288_)) as u8;
                                if v_isSharedCheck_5319_ == 0 {
                                    v___x_5293_ = v_proof_x3f_5288_;
                                    v_isShared_5294_ = v_isSharedCheck_5319_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5291_);
                                    lean_dec(v_proof_x3f_5288_);
                                    v___x_5293_ = lean_box(0);
                                    v_isShared_5294_ = v_isSharedCheck_5319_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_proof_x3f_5288_);
                                lean_dec_ref_known(v_target_x3f_5287_, 1);
                                lean_dec(v_a_5286_);
                                lean_dec(v_acc_5270_);
                                lean_dec_ref(v_lhs_5268_);
                                v___x_5320_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__1);
                                v___x_5321_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_5320_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
                                return v___x_5321_;
                            }
                        } else {
                            lean_dec(v_target_x3f_5287_);
                            lean_dec(v_a_5286_);
                            lean_dec(v_acc_5270_);
                            lean_dec_ref(v_lhs_5268_);
                            v___x_5322_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___closed__2);
                            v___x_5323_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_5322_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
                            return v___x_5323_;
                        }
                    } else {
                        lean_dec(v_acc_5270_);
                        lean_dec_ref(v_lhs_5268_);
                        v_a_5324_ = lean_ctor_get(v___x_5285_, 0);
                        v_isSharedCheck_5331_ = (!lean_is_exclusive(v___x_5285_)) as u8;
                        if v_isSharedCheck_5331_ == 0 {
                            v___x_5326_ = v___x_5285_;
                            v_isShared_5327_ = v_isSharedCheck_5331_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5324_);
                            lean_dec(v___x_5285_);
                            v___x_5326_ = lean_box(0);
                            v_isShared_5327_ = v_isSharedCheck_5331_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_lhs_5268_);
                    v___x_5332_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5332_, 0, v_acc_5270_);
                    return v___x_5332_;
                }
            }
            1 => {
                lean_inc(v_val_5290_);
                v___x_5295_ =
                    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(
                        v_lhs_5268_,
                        v_val_5290_,
                        v_val_5291_,
                        v_flipped_5289_,
                        v_heq_5271_,
                        v_a_5272_,
                        v_a_5273_,
                        v_a_5274_,
                        v_a_5275_,
                        v_a_5276_,
                        v_a_5277_,
                        v_a_5278_,
                        v_a_5279_,
                        v_a_5280_,
                        v_a_5281_,
                    );
                if lean_obj_tag(v___x_5295_) == 0 {
                    v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
                    lean_inc(v_a_5296_);
                    lean_dec_ref_known(v___x_5295_, 1);
                    v___x_5297_ =
                        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(
                            v_acc_5270_,
                            v_a_5296_,
                            v_heq_5271_,
                            v_a_5278_,
                            v_a_5279_,
                            v_a_5280_,
                            v_a_5281_,
                        );
                    if lean_obj_tag(v___x_5297_) == 0 {
                        v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
                        lean_inc(v_a_5298_);
                        lean_dec_ref_known(v___x_5297_, 1);
                        if v_isShared_5294_ == 0 {
                            lean_ctor_set(v___x_5293_, 0, v_a_5298_);
                            v___x_5300_ = v___x_5293_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5298_);
                            v___x_5300_ = v_reuseFailAlloc_5302_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5293_);
                        lean_dec(v_val_5290_);
                        v_a_5303_ = lean_ctor_get(v___x_5297_, 0);
                        v_isSharedCheck_5310_ = (!lean_is_exclusive(v___x_5297_)) as u8;
                        if v_isSharedCheck_5310_ == 0 {
                            v___x_5305_ = v___x_5297_;
                            v_isShared_5306_ = v_isSharedCheck_5310_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5303_);
                            lean_dec(v___x_5297_);
                            v___x_5305_ = lean_box(0);
                            v_isShared_5306_ = v_isSharedCheck_5310_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5293_);
                    lean_dec(v_val_5290_);
                    lean_dec(v_acc_5270_);
                    v_a_5311_ = lean_ctor_get(v___x_5295_, 0);
                    v_isSharedCheck_5318_ = (!lean_is_exclusive(v___x_5295_)) as u8;
                    if v_isSharedCheck_5318_ == 0 {
                        v___x_5313_ = v___x_5295_;
                        v_isShared_5314_ = v_isSharedCheck_5318_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5311_);
                        lean_dec(v___x_5295_);
                        v___x_5313_ = lean_box(0);
                        v_isShared_5314_ = v_isSharedCheck_5318_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_lhs_5268_ = v_val_5290_;
                v_acc_5270_ = v___x_5300_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5306_ == 0 {
                    v___x_5308_ = v___x_5305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
                    v___x_5308_ = v_reuseFailAlloc_5309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5308_;
            }
            5 => {
                if v_isShared_5314_ == 0 {
                    v___x_5316_ = v___x_5313_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5311_);
                    v___x_5316_ = v_reuseFailAlloc_5317_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5316_;
            }
            7 => {
                if v_isShared_5327_ == 0 {
                    v___x_5329_ = v___x_5326_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
                    v___x_5329_ = v_reuseFailAlloc_5330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1()
-> *mut LeanObject {
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    v___x_5334_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5335_ = lean_unsigned_to_nat(29);
    v___x_5336_ = lean_unsigned_to_nat(300);
    v___x_5337_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0;
    v___x_5338_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5339_ = l_mkPanicMessageWithDecl(
        v___x_5338_,
        v___x_5337_,
        v___x_5336_,
        v___x_5335_,
        v___x_5334_,
    );
    return v___x_5339_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2()
-> *mut LeanObject {
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    v___x_5340_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5341_ = lean_unsigned_to_nat(35);
    v___x_5342_ = lean_unsigned_to_nat(299);
    v___x_5343_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__0;
    v___x_5344_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5345_ = l_mkPanicMessageWithDecl(
        v___x_5344_,
        v___x_5343_,
        v___x_5342_,
        v___x_5341_,
        v___x_5340_,
    );
    return v___x_5345_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(
    mut v_rhs_5346_: *mut LeanObject,
    mut v_common_5347_: *mut LeanObject,
    mut v_lhsEqCommon_x3f_5348_: *mut LeanObject,
    mut v_heq_5349_: u8,
    mut v_a_5350_: *mut LeanObject,
    mut v_a_5351_: *mut LeanObject,
    mut v_a_5352_: *mut LeanObject,
    mut v_a_5353_: *mut LeanObject,
    mut v_a_5354_: *mut LeanObject,
    mut v_a_5355_: *mut LeanObject,
    mut v_a_5356_: *mut LeanObject,
    mut v_a_5357_: *mut LeanObject,
    mut v_a_5358_: *mut LeanObject,
    mut v_a_5359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_x3f_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_flipped_5367_: u8 = 0;
    let mut v_val_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5372_: u8 = 0;
    let mut v___y_5374_: u8 = 0;
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5390_: u8 = 0;
    let mut v_a_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5398_: u8 = 0;
    let mut v_a_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5402_: u8 = 0;
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5406_: u8 = 0;
    let mut v___x_5407_: u8 = 0;
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5361_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_rhs_5346_,
                        v_common_5347_,
                    );
                if v___x_5361_ == 0 {
                    v___x_5362_ = lean_st_ref_get(v_a_5350_);
                    lean_inc_ref(v_rhs_5346_);
                    v___x_5363_ = l_Lean_Meta_Grind_Goal_getENode(
                        v___x_5362_,
                        v_rhs_5346_,
                        v_a_5356_,
                        v_a_5357_,
                        v_a_5358_,
                        v_a_5359_,
                    );
                    lean_dec(v___x_5362_);
                    if lean_obj_tag(v___x_5363_) == 0 {
                        v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
                        lean_inc(v_a_5364_);
                        lean_dec_ref_known(v___x_5363_, 1);
                        v_target_x3f_5365_ = lean_ctor_get(v_a_5364_, 4);
                        lean_inc(v_target_x3f_5365_);
                        if lean_obj_tag(v_target_x3f_5365_) == 1 {
                            v_proof_x3f_5366_ = lean_ctor_get(v_a_5364_, 5);
                            lean_inc(v_proof_x3f_5366_);
                            if lean_obj_tag(v_proof_x3f_5366_) == 1 {
                                v_flipped_5367_ = lean_ctor_get_uint8(
                                    v_a_5364_,
                                    (core::mem::size_of::<*mut LeanObject>() * 12) as u32,
                                );
                                lean_dec(v_a_5364_);
                                v_val_5368_ = lean_ctor_get(v_target_x3f_5365_, 0);
                                lean_inc(v_val_5368_);
                                lean_dec_ref_known(v_target_x3f_5365_, 1);
                                v_val_5369_ = lean_ctor_get(v_proof_x3f_5366_, 0);
                                v_isSharedCheck_5408_ =
                                    (!lean_is_exclusive(v_proof_x3f_5366_)) as u8;
                                if v_isSharedCheck_5408_ == 0 {
                                    v___x_5371_ = v_proof_x3f_5366_;
                                    v_isShared_5372_ = v_isSharedCheck_5408_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5369_);
                                    lean_dec(v_proof_x3f_5366_);
                                    v___x_5371_ = lean_box(0);
                                    v_isShared_5372_ = v_isSharedCheck_5408_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_target_x3f_5365_, 1);
                                lean_dec(v_proof_x3f_5366_);
                                lean_dec(v_a_5364_);
                                lean_dec(v_lhsEqCommon_x3f_5348_);
                                lean_dec_ref(v_rhs_5346_);
                                v___x_5409_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__1);
                                v___x_5410_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_5409_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_);
                                return v___x_5410_;
                            }
                        } else {
                            lean_dec(v_target_x3f_5365_);
                            lean_dec(v_a_5364_);
                            lean_dec(v_lhsEqCommon_x3f_5348_);
                            lean_dec_ref(v_rhs_5346_);
                            v___x_5411_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___closed__2);
                            v___x_5412_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom_spec__4(v___x_5411_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_);
                            return v___x_5412_;
                        }
                    } else {
                        lean_dec(v_lhsEqCommon_x3f_5348_);
                        lean_dec_ref(v_rhs_5346_);
                        v_a_5413_ = lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5420_ = (!lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5420_ == 0 {
                            v___x_5415_ = v___x_5363_;
                            v_isShared_5416_ = v_isSharedCheck_5420_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_5413_);
                            lean_dec(v___x_5363_);
                            v___x_5415_ = lean_box(0);
                            v_isShared_5416_ = v_isSharedCheck_5420_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_5346_);
                    v___x_5421_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5421_, 0, v_lhsEqCommon_x3f_5348_);
                    return v___x_5421_;
                }
            }
            1 => {
                if v_flipped_5367_ == 0 {
                    v___x_5407_ = 1;
                    v___y_5374_ = v___x_5407_;
                    state = 2;
                    continue;
                } else {
                    v___y_5374_ = v___x_5361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_val_5368_);
                v___x_5375_ =
                    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(
                        v_val_5368_,
                        v_rhs_5346_,
                        v_val_5369_,
                        v___y_5374_,
                        v_heq_5349_,
                        v_a_5350_,
                        v_a_5351_,
                        v_a_5352_,
                        v_a_5353_,
                        v_a_5354_,
                        v_a_5355_,
                        v_a_5356_,
                        v_a_5357_,
                        v_a_5358_,
                        v_a_5359_,
                    );
                if lean_obj_tag(v___x_5375_) == 0 {
                    v_a_5376_ = lean_ctor_get(v___x_5375_, 0);
                    lean_inc(v_a_5376_);
                    lean_dec_ref_known(v___x_5375_, 1);
                    v___x_5377_ =
                        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(
                            v_val_5368_,
                            v_common_5347_,
                            v_lhsEqCommon_x3f_5348_,
                            v_heq_5349_,
                            v_a_5350_,
                            v_a_5351_,
                            v_a_5352_,
                            v_a_5353_,
                            v_a_5354_,
                            v_a_5355_,
                            v_a_5356_,
                            v_a_5357_,
                            v_a_5358_,
                            v_a_5359_,
                        );
                    if lean_obj_tag(v___x_5377_) == 0 {
                        v_a_5378_ = lean_ctor_get(v___x_5377_, 0);
                        lean_inc(v_a_5378_);
                        lean_dec_ref_known(v___x_5377_, 1);
                        v___x_5379_ =
                            l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkTrans_x27(
                                v_a_5378_,
                                v_a_5376_,
                                v_heq_5349_,
                                v_a_5356_,
                                v_a_5357_,
                                v_a_5358_,
                                v_a_5359_,
                            );
                        if lean_obj_tag(v___x_5379_) == 0 {
                            v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
                            v_isSharedCheck_5390_ = (!lean_is_exclusive(v___x_5379_)) as u8;
                            if v_isSharedCheck_5390_ == 0 {
                                v___x_5382_ = v___x_5379_;
                                v_isShared_5383_ = v_isSharedCheck_5390_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5380_);
                                lean_dec(v___x_5379_);
                                v___x_5382_ = lean_box(0);
                                v_isShared_5383_ = v_isSharedCheck_5390_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5371_);
                            v_a_5391_ = lean_ctor_get(v___x_5379_, 0);
                            v_isSharedCheck_5398_ = (!lean_is_exclusive(v___x_5379_)) as u8;
                            if v_isSharedCheck_5398_ == 0 {
                                v___x_5393_ = v___x_5379_;
                                v_isShared_5394_ = v_isSharedCheck_5398_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5391_);
                                lean_dec(v___x_5379_);
                                v___x_5393_ = lean_box(0);
                                v_isShared_5394_ = v_isSharedCheck_5398_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5376_);
                        lean_del_object(v___x_5371_);
                        return v___x_5377_;
                    }
                } else {
                    lean_del_object(v___x_5371_);
                    lean_dec(v_val_5368_);
                    lean_dec(v_lhsEqCommon_x3f_5348_);
                    v_a_5399_ = lean_ctor_get(v___x_5375_, 0);
                    v_isSharedCheck_5406_ = (!lean_is_exclusive(v___x_5375_)) as u8;
                    if v_isSharedCheck_5406_ == 0 {
                        v___x_5401_ = v___x_5375_;
                        v_isShared_5402_ = v_isSharedCheck_5406_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5399_);
                        lean_dec(v___x_5375_);
                        v___x_5401_ = lean_box(0);
                        v_isShared_5402_ = v_isSharedCheck_5406_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5372_ == 0 {
                    lean_ctor_set(v___x_5371_, 0, v_a_5380_);
                    v___x_5385_ = v___x_5371_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5380_);
                    v___x_5385_ = v_reuseFailAlloc_5389_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5383_ == 0 {
                    lean_ctor_set(v___x_5382_, 0, v___x_5385_);
                    v___x_5387_ = v___x_5382_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5385_);
                    v___x_5387_ = v_reuseFailAlloc_5388_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5387_;
            }
            6 => {
                if v_isShared_5394_ == 0 {
                    v___x_5396_ = v___x_5393_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
                    v___x_5396_ = v_reuseFailAlloc_5397_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5396_;
            }
            8 => {
                if v_isShared_5402_ == 0 {
                    v___x_5404_ = v___x_5401_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5399_);
                    v___x_5404_ = v_reuseFailAlloc_5405_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5404_;
            }
            10 => {
                if v_isShared_5416_ == 0 {
                    v___x_5418_ = v___x_5415_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
                    v___x_5418_ = v_reuseFailAlloc_5419_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3()
-> *mut LeanObject {
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    v___x_5422_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5423_ = lean_unsigned_to_nat(72);
    v___x_5424_ = lean_unsigned_to_nat(321);
    v___x_5425_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__0;
    v___x_5426_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5427_ = l_mkPanicMessageWithDecl(
        v___x_5426_,
        v___x_5425_,
        v___x_5424_,
        v___x_5423_,
        v___x_5422_,
    );
    return v___x_5427_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
    mut v_lhs_5428_: *mut LeanObject,
    mut v_rhs_5429_: *mut LeanObject,
    mut v_heq_5430_: u8,
    mut v_a_5431_: *mut LeanObject,
    mut v_a_5432_: *mut LeanObject,
    mut v_a_5433_: *mut LeanObject,
    mut v_a_5434_: *mut LeanObject,
    mut v_a_5435_: *mut LeanObject,
    mut v_a_5436_: *mut LeanObject,
    mut v_a_5437_: *mut LeanObject,
    mut v_a_5438_: *mut LeanObject,
    mut v_a_5439_: *mut LeanObject,
    mut v_a_5440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5442_: u8 = 0;
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: u8 = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_heqProofs_5458_: u8 = 0;
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v_val_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5472_: u8 = 0;
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_a_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5482_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5486_: u8 = 0;
    let mut v_a_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_a_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
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
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5442_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_lhs_5428_,
                        v_rhs_5429_,
                    );
                if v___x_5442_ == 0 {
                    lean_inc_ref(v_lhs_5428_);
                    v___x_5443_ = l_Lean_Meta_Grind_getRootENode___redArg(
                        v_lhs_5428_,
                        v_a_5431_,
                        v_a_5437_,
                        v_a_5438_,
                        v_a_5439_,
                        v_a_5440_,
                    );
                    if lean_obj_tag(v___x_5443_) == 0 {
                        v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
                        lean_inc(v_a_5444_);
                        lean_dec_ref_known(v___x_5443_, 1);
                        v___x_5445_ = lean_st_ref_get(v_a_5431_);
                        lean_inc_ref(v_lhs_5428_);
                        v___x_5446_ = l_Lean_Meta_Grind_Goal_getENode(
                            v___x_5445_,
                            v_lhs_5428_,
                            v_a_5437_,
                            v_a_5438_,
                            v_a_5439_,
                            v_a_5440_,
                        );
                        lean_dec(v___x_5445_);
                        if lean_obj_tag(v___x_5446_) == 0 {
                            v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
                            lean_inc(v_a_5447_);
                            lean_dec_ref_known(v___x_5446_, 1);
                            v___x_5448_ = lean_st_ref_get(v_a_5431_);
                            lean_inc_ref(v_rhs_5429_);
                            v___x_5449_ = l_Lean_Meta_Grind_Goal_getENode(
                                v___x_5448_,
                                v_rhs_5429_,
                                v_a_5437_,
                                v_a_5438_,
                                v_a_5439_,
                                v_a_5440_,
                            );
                            lean_dec(v___x_5448_);
                            if lean_obj_tag(v___x_5449_) == 0 {
                                v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
                                lean_inc(v_a_5450_);
                                lean_dec_ref_known(v___x_5449_, 1);
                                v_root_5451_ = lean_ctor_get(v_a_5447_, 2);
                                lean_inc_ref(v_root_5451_);
                                lean_dec(v_a_5447_);
                                v_root_5452_ = lean_ctor_get(v_a_5450_, 2);
                                lean_inc_ref(v_root_5452_);
                                lean_dec(v_a_5450_);
                                v___x_5453_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_5451_, v_root_5452_);
                                lean_dec_ref(v_root_5452_);
                                lean_dec_ref(v_root_5451_);
                                if v___x_5453_ == 0 {
                                    lean_dec(v_a_5444_);
                                    lean_dec_ref(v_rhs_5429_);
                                    lean_dec_ref(v_lhs_5428_);
                                    v___x_5454_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__2);
                                    v___x_5455_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5454_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
                                    return v___x_5455_;
                                } else {
                                    lean_inc_ref(v_rhs_5429_);
                                    lean_inc_ref(v_lhs_5428_);
                                    v___x_5456_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon(v_lhs_5428_, v_rhs_5429_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
                                    if lean_obj_tag(v___x_5456_) == 0 {
                                        v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
                                        lean_inc(v_a_5457_);
                                        lean_dec_ref_known(v___x_5456_, 1);
                                        v_heqProofs_5458_ = lean_ctor_get_uint8(
                                            v_a_5444_,
                                            (core::mem::size_of::<*mut LeanObject>() * 12 + 4)
                                                as u32,
                                        );
                                        lean_dec(v_a_5444_);
                                        v___x_5459_ = lean_box(0);
                                        v___x_5460_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(v_lhs_5428_, v_a_5457_, v___x_5459_, v_heqProofs_5458_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
                                        if lean_obj_tag(v___x_5460_) == 0 {
                                            v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
                                            lean_inc(v_a_5461_);
                                            lean_dec_ref_known(v___x_5460_, 1);
                                            v___x_5462_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(v_rhs_5429_, v_a_5457_, v_a_5461_, v_heqProofs_5458_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
                                            lean_dec(v_a_5457_);
                                            if lean_obj_tag(v___x_5462_) == 0 {
                                                v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
                                                v_isSharedCheck_5478_ =
                                                    (!lean_is_exclusive(v___x_5462_)) as u8;
                                                if v_isSharedCheck_5478_ == 0 {
                                                    v___x_5465_ = v___x_5462_;
                                                    v_isShared_5466_ = v_isSharedCheck_5478_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5463_);
                                                    lean_dec(v___x_5462_);
                                                    v___x_5465_ = lean_box(0);
                                                    v_isShared_5466_ = v_isSharedCheck_5478_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5479_ = lean_ctor_get(v___x_5462_, 0);
                                                v_isSharedCheck_5486_ =
                                                    (!lean_is_exclusive(v___x_5462_)) as u8;
                                                if v_isSharedCheck_5486_ == 0 {
                                                    v___x_5481_ = v___x_5462_;
                                                    v_isShared_5482_ = v_isSharedCheck_5486_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5479_);
                                                    lean_dec(v___x_5462_);
                                                    v___x_5481_ = lean_box(0);
                                                    v_isShared_5482_ = v_isSharedCheck_5486_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_5457_);
                                            lean_dec_ref(v_rhs_5429_);
                                            v_a_5487_ = lean_ctor_get(v___x_5460_, 0);
                                            v_isSharedCheck_5494_ =
                                                (!lean_is_exclusive(v___x_5460_)) as u8;
                                            if v_isSharedCheck_5494_ == 0 {
                                                v___x_5489_ = v___x_5460_;
                                                v_isShared_5490_ = v_isSharedCheck_5494_;
                                                state = 7;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5487_);
                                                lean_dec(v___x_5460_);
                                                v___x_5489_ = lean_box(0);
                                                v_isShared_5490_ = v_isSharedCheck_5494_;
                                                state = 7;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5444_);
                                        lean_dec_ref(v_rhs_5429_);
                                        lean_dec_ref(v_lhs_5428_);
                                        return v___x_5456_;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5447_);
                                lean_dec(v_a_5444_);
                                lean_dec_ref(v_rhs_5429_);
                                lean_dec_ref(v_lhs_5428_);
                                v_a_5495_ = lean_ctor_get(v___x_5449_, 0);
                                v_isSharedCheck_5502_ = (!lean_is_exclusive(v___x_5449_)) as u8;
                                if v_isSharedCheck_5502_ == 0 {
                                    v___x_5497_ = v___x_5449_;
                                    v_isShared_5498_ = v_isSharedCheck_5502_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5495_);
                                    lean_dec(v___x_5449_);
                                    v___x_5497_ = lean_box(0);
                                    v_isShared_5498_ = v_isSharedCheck_5502_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5444_);
                            lean_dec_ref(v_rhs_5429_);
                            lean_dec_ref(v_lhs_5428_);
                            v_a_5503_ = lean_ctor_get(v___x_5446_, 0);
                            v_isSharedCheck_5510_ = (!lean_is_exclusive(v___x_5446_)) as u8;
                            if v_isSharedCheck_5510_ == 0 {
                                v___x_5505_ = v___x_5446_;
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_5503_);
                                lean_dec(v___x_5446_);
                                v___x_5505_ = lean_box(0);
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_rhs_5429_);
                        lean_dec_ref(v_lhs_5428_);
                        v_a_5511_ = lean_ctor_get(v___x_5443_, 0);
                        v_isSharedCheck_5518_ = (!lean_is_exclusive(v___x_5443_)) as u8;
                        if v_isSharedCheck_5518_ == 0 {
                            v___x_5513_ = v___x_5443_;
                            v_isShared_5514_ = v_isSharedCheck_5518_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5511_);
                            lean_dec(v___x_5443_);
                            v___x_5513_ = lean_box(0);
                            v_isShared_5514_ = v_isSharedCheck_5518_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_5429_);
                    v___x_5519_ =
                        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkRefl(
                            v_lhs_5428_,
                            v_heq_5430_,
                            v_a_5437_,
                            v_a_5438_,
                            v_a_5439_,
                            v_a_5440_,
                        );
                    return v___x_5519_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_5463_) == 1 {
                    v_val_5467_ = lean_ctor_get(v_a_5463_, 0);
                    lean_inc(v_val_5467_);
                    lean_dec_ref_known(v_a_5463_, 1);
                    if v_heq_5430_ == 0 {
                        if v_heqProofs_5458_ == 0 {
                            v___y_5472_ = v___x_5453_;
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_5465_);
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_5472_ = v_heqProofs_5458_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5465_);
                    lean_dec(v_a_5463_);
                    v___x_5476_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___closed__3);
                    v___x_5477_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5476_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
                    return v___x_5477_;
                }
            }
            2 => {
                if v_heq_5430_ == 0 {
                    v___x_5469_ = l_Lean_Meta_mkEqOfHEq(
                        v_val_5467_,
                        v_heq_5430_,
                        v_a_5437_,
                        v_a_5438_,
                        v_a_5439_,
                        v_a_5440_,
                    );
                    return v___x_5469_;
                } else {
                    v___x_5470_ = l_Lean_Meta_mkHEqOfEq(
                        v_val_5467_,
                        v_a_5437_,
                        v_a_5438_,
                        v_a_5439_,
                        v_a_5440_,
                    );
                    return v___x_5470_;
                }
            }
            3 => {
                if v___y_5472_ == 0 {
                    lean_del_object(v___x_5465_);
                    state = 2;
                    continue;
                } else {
                    if v_isShared_5466_ == 0 {
                        lean_ctor_set(v___x_5465_, 0, v_val_5467_);
                        v___x_5474_ = v___x_5465_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_val_5467_);
                        v___x_5474_ = v_reuseFailAlloc_5475_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5474_;
            }
            5 => {
                if v_isShared_5482_ == 0 {
                    v___x_5484_ = v___x_5481_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_a_5479_);
                    v___x_5484_ = v_reuseFailAlloc_5485_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5484_;
            }
            7 => {
                if v_isShared_5490_ == 0 {
                    v___x_5492_ = v___x_5489_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
                    v___x_5492_ = v_reuseFailAlloc_5493_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5492_;
            }
            9 => {
                if v_isShared_5498_ == 0 {
                    v___x_5500_ = v___x_5497_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5500_;
            }
            11 => {
                if v_isShared_5506_ == 0 {
                    v___x_5508_ = v___x_5505_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
                    v___x_5508_ = v_reuseFailAlloc_5509_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5508_;
            }
            13 => {
                if v_isShared_5514_ == 0 {
                    v___x_5516_ = v___x_5513_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
                    v___x_5516_ = v_reuseFailAlloc_5517_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(
    mut v_thm_5520_: *mut LeanObject,
    mut v_lhs_5521_: *mut LeanObject,
    mut v_rhs_5522_: *mut LeanObject,
    mut v_i_5523_: *mut LeanObject,
    mut v_a_5524_: *mut LeanObject,
    mut v_a_5525_: *mut LeanObject,
    mut v_a_5526_: *mut LeanObject,
    mut v_a_5527_: *mut LeanObject,
    mut v_a_5528_: *mut LeanObject,
    mut v_a_5529_: *mut LeanObject,
    mut v_a_5530_: *mut LeanObject,
    mut v_a_5531_: *mut LeanObject,
    mut v_a_5532_: *mut LeanObject,
    mut v_a_5533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: u8 = 0;
    let mut v_proof_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argKinds_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: u8 = 0;
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5554_: u8 = 0;
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5559_: u8 = 0;
    let mut v___x_5560_: u8 = 0;
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: u8 = 0;
    let mut v___x_5564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5535_ = lean_unsigned_to_nat(0);
                v___x_5536_ = lean_nat_dec_lt(v___x_5535_, v_i_5523_);
                if v___x_5536_ == 0 {
                    v_proof_5537_ = lean_ctor_get(v_thm_5520_, 1);
                    lean_inc_ref(v_proof_5537_);
                    v___x_5538_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5538_, 0, v_proof_5537_);
                    return v___x_5538_;
                } else {
                    v___x_5539_ = lean_unsigned_to_nat(1);
                    v_i_5540_ = lean_nat_sub(v_i_5523_, v___x_5539_);
                    v___x_5541_ = l_Lean_Expr_appFn_x21(v_lhs_5521_);
                    v___x_5542_ = l_Lean_Expr_appFn_x21(v_rhs_5522_);
                    v___x_5543_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_thm_5520_, v___x_5541_, v___x_5542_, v_i_5540_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
                    lean_dec_ref(v___x_5542_);
                    lean_dec_ref(v___x_5541_);
                    if lean_obj_tag(v___x_5543_) == 0 {
                        v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
                        lean_inc(v_a_5544_);
                        lean_dec_ref_known(v___x_5543_, 1);
                        v_argKinds_5545_ = lean_ctor_get(v_thm_5520_, 2);
                        v___x_5546_ = l_Lean_Expr_appArg_x21(v_lhs_5521_);
                        v___x_5547_ = l_Lean_Expr_appArg_x21(v_rhs_5522_);
                        v___x_5560_ = 0;
                        v___x_5561_ = lean_box((v___x_5560_) as usize);
                        v___x_5562_ = lean_array_get(v___x_5561_, v_argKinds_5545_, v_i_5540_);
                        lean_dec(v_i_5540_);
                        lean_dec(v___x_5561_);
                        v___x_5563_ = (lean_unbox(v___x_5562_) as u8);
                        lean_dec(v___x_5562_);
                        if v___x_5563_ == 4 {
                            v___y_5549_ = v___x_5536_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5564_ = 0;
                            v___y_5549_ = v___x_5564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_5540_);
                        return v___x_5543_;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___x_5547_);
                lean_inc_ref(v___x_5546_);
                v___x_5550_ =
                    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
                        v___x_5546_,
                        v___x_5547_,
                        v___y_5549_,
                        v_a_5524_,
                        v_a_5525_,
                        v_a_5526_,
                        v_a_5527_,
                        v_a_5528_,
                        v_a_5529_,
                        v_a_5530_,
                        v_a_5531_,
                        v_a_5532_,
                        v_a_5533_,
                    );
                if lean_obj_tag(v___x_5550_) == 0 {
                    v_a_5551_ = lean_ctor_get(v___x_5550_, 0);
                    v_isSharedCheck_5559_ = (!lean_is_exclusive(v___x_5550_)) as u8;
                    if v_isSharedCheck_5559_ == 0 {
                        v___x_5553_ = v___x_5550_;
                        v_isShared_5554_ = v_isSharedCheck_5559_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5551_);
                        lean_dec(v___x_5550_);
                        v___x_5553_ = lean_box(0);
                        v_isShared_5554_ = v_isSharedCheck_5559_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5547_);
                    lean_dec_ref(v___x_5546_);
                    lean_dec(v_a_5544_);
                    return v___x_5550_;
                }
            }
            2 => {
                v___x_5555_ = l_Lean_mkApp3(v_a_5544_, v___x_5546_, v___x_5547_, v_a_5551_);
                if v_isShared_5554_ == 0 {
                    lean_ctor_set(v___x_5553_, 0, v___x_5555_);
                    v___x_5557_ = v___x_5553_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5555_);
                    v___x_5557_ = v_reuseFailAlloc_5558_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(
    mut v_f_5568_: *mut LeanObject,
    mut v_g_5569_: *mut LeanObject,
    mut v_numArgs_5570_: *mut LeanObject,
    mut v_lhs_5571_: *mut LeanObject,
    mut v_rhs_5572_: *mut LeanObject,
    mut v_heq_5573_: u8,
    mut v_a_5574_: *mut LeanObject,
    mut v_a_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
    mut v_a_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
    mut v_a_5579_: *mut LeanObject,
    mut v_a_5580_: *mut LeanObject,
    mut v_a_5581_: *mut LeanObject,
    mut v_a_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_argKinds_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: u8 = 0;
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5613_: u8 = 0;
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5617_: u8 = 0;
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
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
                lean_inc(v_numArgs_5570_);
                lean_inc_ref(v_f_5568_);
                v___x_5585_ = l_Lean_Meta_Grind_mkHCongrWithArity___redArg(
                    v_f_5568_,
                    v_numArgs_5570_,
                    v_a_5577_,
                    v_a_5580_,
                    v_a_5581_,
                    v_a_5582_,
                    v_a_5583_,
                );
                if lean_obj_tag(v___x_5585_) == 0 {
                    v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
                    lean_inc(v_a_5586_);
                    lean_dec_ref_known(v___x_5585_, 1);
                    v_argKinds_5587_ = lean_ctor_get(v_a_5586_, 2);
                    v___x_5588_ = lean_array_get_size(v_argKinds_5587_);
                    v___x_5589_ = lean_nat_dec_eq(v___x_5588_, v_numArgs_5570_);
                    if v___x_5589_ == 0 {
                        lean_dec(v_a_5586_);
                        lean_dec_ref(v_rhs_5572_);
                        lean_dec_ref(v_lhs_5571_);
                        lean_dec(v_numArgs_5570_);
                        lean_dec_ref(v_g_5569_);
                        lean_dec_ref(v_f_5568_);
                        v___x_5590_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__2);
                        v___x_5591_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5590_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
                        return v___x_5591_;
                    } else {
                        v___x_5592_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(v_a_5586_, v_lhs_5571_, v_rhs_5572_, v_numArgs_5570_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
                        lean_dec(v_a_5586_);
                        if lean_obj_tag(v___x_5592_) == 0 {
                            v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
                            lean_inc(v_a_5593_);
                            lean_dec_ref_known(v___x_5592_, 1);
                            v___x_5594_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_5568_, v_g_5569_);
                            if v___x_5594_ == 0 {
                                v___x_5595_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___closed__4;
                                v___x_5596_ =
                                    l_Lean_Core_mkFreshUserName(v___x_5595_, v_a_5582_, v_a_5583_);
                                if lean_obj_tag(v___x_5596_) == 0 {
                                    v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
                                    lean_inc(v_a_5597_);
                                    lean_dec_ref_known(v___x_5596_, 1);
                                    lean_inc(v_a_5583_);
                                    lean_inc_ref(v_a_5582_);
                                    lean_inc(v_a_5581_);
                                    lean_inc_ref(v_a_5580_);
                                    lean_inc_ref(v_f_5568_);
                                    v___x_5598_ = lean_infer_type(
                                        v_f_5568_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_,
                                    );
                                    if lean_obj_tag(v___x_5598_) == 0 {
                                        v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
                                        lean_inc(v_a_5599_);
                                        lean_dec_ref_known(v___x_5598_, 1);
                                        v___x_5600_ = lean_box((v___x_5594_) as usize);
                                        v___x_5601_ = lean_box((v___x_5589_) as usize);
                                        v___f_5602_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___lam__0___boxed as *mut core::ffi::c_void, 17, 5);
                                        lean_closure_set(v___f_5602_, 0, v_numArgs_5570_);
                                        lean_closure_set(v___f_5602_, 1, v_rhs_5572_);
                                        lean_closure_set(v___f_5602_, 2, v_lhs_5571_);
                                        lean_closure_set(v___f_5602_, 3, v___x_5600_);
                                        lean_closure_set(v___f_5602_, 4, v___x_5601_);
                                        v___x_5603_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_a_5597_, v_a_5599_, v___f_5602_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
                                        if lean_obj_tag(v___x_5603_) == 0 {
                                            v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
                                            lean_inc(v_a_5604_);
                                            lean_dec_ref_known(v___x_5603_, 1);
                                            v___x_5605_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(v_f_5568_, v_g_5569_, v___x_5594_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
                                            if lean_obj_tag(v___x_5605_) == 0 {
                                                v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
                                                lean_inc(v_a_5606_);
                                                lean_dec_ref_known(v___x_5605_, 1);
                                                v___x_5607_ = l_Lean_Meta_mkEqNDRec(
                                                    v_a_5604_, v_a_5593_, v_a_5606_, v_a_5580_,
                                                    v_a_5581_, v_a_5582_, v_a_5583_,
                                                );
                                                if lean_obj_tag(v___x_5607_) == 0 {
                                                    v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
                                                    lean_inc(v_a_5608_);
                                                    lean_dec_ref_known(v___x_5607_, 1);
                                                    v___x_5609_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_5608_, v_heq_5573_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
                                                    return v___x_5609_;
                                                } else {
                                                    return v___x_5607_;
                                                }
                                            } else {
                                                lean_dec(v_a_5604_);
                                                lean_dec(v_a_5593_);
                                                return v___x_5605_;
                                            }
                                        } else {
                                            lean_dec(v_a_5593_);
                                            lean_dec_ref(v_g_5569_);
                                            lean_dec_ref(v_f_5568_);
                                            return v___x_5603_;
                                        }
                                    } else {
                                        lean_dec(v_a_5597_);
                                        lean_dec(v_a_5593_);
                                        lean_dec_ref(v_rhs_5572_);
                                        lean_dec_ref(v_lhs_5571_);
                                        lean_dec(v_numArgs_5570_);
                                        lean_dec_ref(v_g_5569_);
                                        lean_dec_ref(v_f_5568_);
                                        return v___x_5598_;
                                    }
                                } else {
                                    lean_dec(v_a_5593_);
                                    lean_dec_ref(v_rhs_5572_);
                                    lean_dec_ref(v_lhs_5571_);
                                    lean_dec(v_numArgs_5570_);
                                    lean_dec_ref(v_g_5569_);
                                    lean_dec_ref(v_f_5568_);
                                    v_a_5610_ = lean_ctor_get(v___x_5596_, 0);
                                    v_isSharedCheck_5617_ = (!lean_is_exclusive(v___x_5596_)) as u8;
                                    if v_isSharedCheck_5617_ == 0 {
                                        v___x_5612_ = v___x_5596_;
                                        v_isShared_5613_ = v_isSharedCheck_5617_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5610_);
                                        lean_dec(v___x_5596_);
                                        v___x_5612_ = lean_box(0);
                                        v_isShared_5613_ = v_isSharedCheck_5617_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_rhs_5572_);
                                lean_dec_ref(v_lhs_5571_);
                                lean_dec(v_numArgs_5570_);
                                lean_dec_ref(v_g_5569_);
                                lean_dec_ref(v_f_5568_);
                                v___x_5618_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqOfHEqIfNeeded(v_a_5593_, v_heq_5573_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
                                return v___x_5618_;
                            }
                        } else {
                            lean_dec_ref(v_rhs_5572_);
                            lean_dec_ref(v_lhs_5571_);
                            lean_dec(v_numArgs_5570_);
                            lean_dec_ref(v_g_5569_);
                            lean_dec_ref(v_f_5568_);
                            return v___x_5592_;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhs_5572_);
                    lean_dec_ref(v_lhs_5571_);
                    lean_dec(v_numArgs_5570_);
                    lean_dec_ref(v_g_5569_);
                    lean_dec_ref(v_f_5568_);
                    v_a_5619_ = lean_ctor_get(v___x_5585_, 0);
                    v_isSharedCheck_5626_ = (!lean_is_exclusive(v___x_5585_)) as u8;
                    if v_isSharedCheck_5626_ == 0 {
                        v___x_5621_ = v___x_5585_;
                        v_isShared_5622_ = v_isSharedCheck_5626_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5619_);
                        lean_dec(v___x_5585_);
                        v___x_5621_ = lean_box(0);
                        v_isShared_5622_ = v_isSharedCheck_5626_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5613_ == 0 {
                    v___x_5615_ = v___x_5612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5610_);
                    v___x_5615_ = v_reuseFailAlloc_5616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5615_;
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
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1()
-> *mut LeanObject {
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    v___x_5628_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5629_ = lean_unsigned_to_nat(27);
    v___x_5630_ = lean_unsigned_to_nat(237);
    v___x_5631_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0;
    v___x_5632_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5633_ = l_mkPanicMessageWithDecl(
        v___x_5632_,
        v___x_5631_,
        v___x_5630_,
        v___x_5629_,
        v___x_5628_,
    );
    return v___x_5633_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2()
-> *mut LeanObject {
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    v___x_5634_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__2;
    v___x_5635_ = lean_unsigned_to_nat(27);
    v___x_5636_ = lean_unsigned_to_nat(236);
    v___x_5637_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__0;
    v___x_5638_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__4___redArg___closed__0;
    v___x_5639_ = l_mkPanicMessageWithDecl(
        v___x_5638_,
        v___x_5637_,
        v___x_5636_,
        v___x_5635_,
        v___x_5634_,
    );
    return v___x_5639_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(
    mut v_lhs_5640_: *mut LeanObject,
    mut v_rhs_5641_: *mut LeanObject,
    mut v_heq_5642_: u8,
    mut v_e_u2081_5643_: *mut LeanObject,
    mut v_e_u2082_5644_: *mut LeanObject,
    mut v_numArgs_5645_: *mut LeanObject,
    mut v_a_5646_: *mut LeanObject,
    mut v_a_5647_: *mut LeanObject,
    mut v_a_5648_: *mut LeanObject,
    mut v_a_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_a_5651_: *mut LeanObject,
    mut v_a_5652_: *mut LeanObject,
    mut v_a_5653_: *mut LeanObject,
    mut v_a_5654_: *mut LeanObject,
    mut v_a_5655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numArgs_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: u8 = 0;
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: u8 = 0;
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5670_: u8 = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5674_: u8 = 0;
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_u2081_5643_) == 5 {
                    if lean_obj_tag(v_e_u2082_5644_) == 5 {
                        v_fn_5657_ = lean_ctor_get(v_e_u2081_5643_, 0);
                        lean_inc_ref(v_fn_5657_);
                        lean_dec_ref_known(v_e_u2081_5643_, 2);
                        v_fn_5658_ = lean_ctor_get(v_e_u2082_5644_, 0);
                        lean_inc_ref(v_fn_5658_);
                        lean_dec_ref_known(v_e_u2082_5644_, 2);
                        v___x_5659_ = lean_unsigned_to_nat(1);
                        v_numArgs_5660_ = lean_nat_add(v_numArgs_5645_, v___x_5659_);
                        lean_dec(v_numArgs_5645_);
                        v___x_5661_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_fn_5657_, v_fn_5658_,
                            );
                        if v___x_5661_ == 0 {
                            lean_inc_ref(v_fn_5658_);
                            lean_inc_ref(v_fn_5657_);
                            v___x_5662_ = l_Lean_Meta_Grind_hasSameType(
                                v_fn_5657_, v_fn_5658_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_,
                            );
                            if lean_obj_tag(v___x_5662_) == 0 {
                                v_a_5663_ = lean_ctor_get(v___x_5662_, 0);
                                lean_inc(v_a_5663_);
                                lean_dec_ref_known(v___x_5662_, 1);
                                v___x_5664_ = (lean_unbox(v_a_5663_) as u8);
                                lean_dec(v_a_5663_);
                                if v___x_5664_ == 0 {
                                    v_e_u2081_5643_ = v_fn_5657_;
                                    v_e_u2082_5644_ = v_fn_5658_;
                                    v_numArgs_5645_ = v_numArgs_5660_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_5666_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_5657_, v_fn_5658_, v_numArgs_5660_, v_lhs_5640_, v_rhs_5641_, v_heq_5642_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_);
                                    return v___x_5666_;
                                }
                            } else {
                                lean_dec(v_numArgs_5660_);
                                lean_dec_ref(v_fn_5658_);
                                lean_dec_ref(v_fn_5657_);
                                lean_dec_ref(v_rhs_5641_);
                                lean_dec_ref(v_lhs_5640_);
                                v_a_5667_ = lean_ctor_get(v___x_5662_, 0);
                                v_isSharedCheck_5674_ = (!lean_is_exclusive(v___x_5662_)) as u8;
                                if v_isSharedCheck_5674_ == 0 {
                                    v___x_5669_ = v___x_5662_;
                                    v_isShared_5670_ = v_isSharedCheck_5674_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_5667_);
                                    lean_dec(v___x_5662_);
                                    v___x_5669_ = lean_box(0);
                                    v_isShared_5670_ = v_isSharedCheck_5674_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_5675_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(v_fn_5657_, v_fn_5658_, v_numArgs_5660_, v_lhs_5640_, v_rhs_5641_, v_heq_5642_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_);
                            return v___x_5675_;
                        }
                    } else {
                        lean_dec_ref_known(v_e_u2081_5643_, 2);
                        lean_dec(v_numArgs_5645_);
                        lean_dec_ref(v_e_u2082_5644_);
                        lean_dec_ref(v_rhs_5641_);
                        lean_dec_ref(v_lhs_5640_);
                        v___x_5676_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__1);
                        v___x_5677_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5676_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_);
                        return v___x_5677_;
                    }
                } else {
                    lean_dec(v_numArgs_5645_);
                    lean_dec_ref(v_e_u2082_5644_);
                    lean_dec_ref(v_e_u2081_5643_);
                    lean_dec_ref(v_rhs_5641_);
                    lean_dec_ref(v_lhs_5640_);
                    v___x_5678_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___closed__2);
                    v___x_5679_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_findCommon_spec__5(v___x_5678_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_);
                    return v___x_5679_;
                }
            }
            1 => {
                if v_isShared_5670_ == 0 {
                    v___x_5672_ = v___x_5669_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_a_5667_);
                    v___x_5672_ = v_reuseFailAlloc_5673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(
    mut v_lhs_5680_: *mut LeanObject,
    mut v_rhs_5681_: *mut LeanObject,
    mut v_heq_5682_: u8,
    mut v_a_5683_: *mut LeanObject,
    mut v_a_5684_: *mut LeanObject,
    mut v_a_5685_: *mut LeanObject,
    mut v_a_5686_: *mut LeanObject,
    mut v_a_5687_: *mut LeanObject,
    mut v_a_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
    mut v_a_5690_: *mut LeanObject,
    mut v_a_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    v___x_5694_ = lean_unsigned_to_nat(0);
    lean_inc_ref(v_rhs_5681_);
    lean_inc_ref(v_lhs_5680_);
    v___x_5695_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(
        v_lhs_5680_,
        v_rhs_5681_,
        v_heq_5682_,
        v_lhs_5680_,
        v_rhs_5681_,
        v___x_5694_,
        v_a_5683_,
        v_a_5684_,
        v_a_5685_,
        v_a_5686_,
        v_a_5687_,
        v_a_5688_,
        v_a_5689_,
        v_a_5690_,
        v_a_5691_,
        v_a_5692_,
    );
    return v___x_5695_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC___boxed(
    mut v_lhs_5696_: *mut LeanObject,
    mut v_rhs_5697_: *mut LeanObject,
    mut v_heq_5698_: *mut LeanObject,
    mut v_a_5699_: *mut LeanObject,
    mut v_a_5700_: *mut LeanObject,
    mut v_a_5701_: *mut LeanObject,
    mut v_a_5702_: *mut LeanObject,
    mut v_a_5703_: *mut LeanObject,
    mut v_a_5704_: *mut LeanObject,
    mut v_a_5705_: *mut LeanObject,
    mut v_a_5706_: *mut LeanObject,
    mut v_a_5707_: *mut LeanObject,
    mut v_a_5708_: *mut LeanObject,
    mut v_a_5709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5710_: u8 = 0;
    let mut v_res_5711_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5710_ = (lean_unbox(v_heq_5698_) as u8);
    v_res_5711_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC(
        v_lhs_5696_,
        v_rhs_5697_,
        v_heq_boxed_5710_,
        v_a_5699_,
        v_a_5700_,
        v_a_5701_,
        v_a_5702_,
        v_a_5703_,
        v_a_5704_,
        v_a_5705_,
        v_a_5706_,
        v_a_5707_,
        v_a_5708_,
    );
    lean_dec(v_a_5708_);
    lean_dec_ref(v_a_5707_);
    lean_dec(v_a_5706_);
    lean_dec_ref(v_a_5705_);
    lean_dec(v_a_5704_);
    lean_dec_ref(v_a_5703_);
    lean_dec(v_a_5702_);
    lean_dec_ref(v_a_5701_);
    lean_dec(v_a_5700_);
    lean_dec(v_a_5699_);
    return v_res_5711_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr___boxed(
    mut v_lhs_5712_: *mut LeanObject,
    mut v_rhs_5713_: *mut LeanObject,
    mut v_heq_5714_: *mut LeanObject,
    mut v_a_5715_: *mut LeanObject,
    mut v_a_5716_: *mut LeanObject,
    mut v_a_5717_: *mut LeanObject,
    mut v_a_5718_: *mut LeanObject,
    mut v_a_5719_: *mut LeanObject,
    mut v_a_5720_: *mut LeanObject,
    mut v_a_5721_: *mut LeanObject,
    mut v_a_5722_: *mut LeanObject,
    mut v_a_5723_: *mut LeanObject,
    mut v_a_5724_: *mut LeanObject,
    mut v_a_5725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5726_: u8 = 0;
    let mut v_res_5727_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5726_ = (lean_unbox(v_heq_5714_) as u8);
    v_res_5727_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedDecidableCongr(
            v_lhs_5712_,
            v_rhs_5713_,
            v_heq_boxed_5726_,
            v_a_5715_,
            v_a_5716_,
            v_a_5717_,
            v_a_5718_,
            v_a_5719_,
            v_a_5720_,
            v_a_5721_,
            v_a_5722_,
            v_a_5723_,
            v_a_5724_,
        );
    lean_dec(v_a_5724_);
    lean_dec_ref(v_a_5723_);
    lean_dec(v_a_5722_);
    lean_dec_ref(v_a_5721_);
    lean_dec(v_a_5720_);
    lean_dec_ref(v_a_5719_);
    lean_dec(v_a_5718_);
    lean_dec_ref(v_a_5717_);
    lean_dec(v_a_5716_);
    lean_dec(v_a_5715_);
    lean_dec_ref(v_rhs_5713_);
    lean_dec_ref(v_lhs_5712_);
    return v_res_5727_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr___boxed(
    mut v_lhs_5728_: *mut LeanObject,
    mut v_rhs_5729_: *mut LeanObject,
    mut v_heq_5730_: *mut LeanObject,
    mut v_a_5731_: *mut LeanObject,
    mut v_a_5732_: *mut LeanObject,
    mut v_a_5733_: *mut LeanObject,
    mut v_a_5734_: *mut LeanObject,
    mut v_a_5735_: *mut LeanObject,
    mut v_a_5736_: *mut LeanObject,
    mut v_a_5737_: *mut LeanObject,
    mut v_a_5738_: *mut LeanObject,
    mut v_a_5739_: *mut LeanObject,
    mut v_a_5740_: *mut LeanObject,
    mut v_a_5741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5742_: u8 = 0;
    let mut v_res_5743_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5742_ = (lean_unbox(v_heq_5730_) as u8);
    v_res_5743_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkNestedProofCongr(
        v_lhs_5728_,
        v_rhs_5729_,
        v_heq_boxed_5742_,
        v_a_5731_,
        v_a_5732_,
        v_a_5733_,
        v_a_5734_,
        v_a_5735_,
        v_a_5736_,
        v_a_5737_,
        v_a_5738_,
        v_a_5739_,
        v_a_5740_,
    );
    lean_dec(v_a_5740_);
    lean_dec_ref(v_a_5739_);
    lean_dec(v_a_5738_);
    lean_dec_ref(v_a_5737_);
    lean_dec(v_a_5736_);
    lean_dec_ref(v_a_5735_);
    lean_dec(v_a_5734_);
    lean_dec_ref(v_a_5733_);
    lean_dec(v_a_5732_);
    lean_dec(v_a_5731_);
    lean_dec_ref(v_rhs_5729_);
    lean_dec_ref(v_lhs_5728_);
    return v_res_5743_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof___boxed(
    mut v_lhs_5744_: *mut LeanObject,
    mut v_rhs_5745_: *mut LeanObject,
    mut v_h_5746_: *mut LeanObject,
    mut v_flipped_5747_: *mut LeanObject,
    mut v_heq_5748_: *mut LeanObject,
    mut v_a_5749_: *mut LeanObject,
    mut v_a_5750_: *mut LeanObject,
    mut v_a_5751_: *mut LeanObject,
    mut v_a_5752_: *mut LeanObject,
    mut v_a_5753_: *mut LeanObject,
    mut v_a_5754_: *mut LeanObject,
    mut v_a_5755_: *mut LeanObject,
    mut v_a_5756_: *mut LeanObject,
    mut v_a_5757_: *mut LeanObject,
    mut v_a_5758_: *mut LeanObject,
    mut v_a_5759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flipped_boxed_5760_: u8 = 0;
    let mut v_heq_boxed_5761_: u8 = 0;
    let mut v_res_5762_: *mut LeanObject = core::ptr::null_mut();
    v_flipped_boxed_5760_ = (lean_unbox(v_flipped_5747_) as u8);
    v_heq_boxed_5761_ = (lean_unbox(v_heq_5748_) as u8);
    v_res_5762_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_realizeEqProof(
        v_lhs_5744_,
        v_rhs_5745_,
        v_h_5746_,
        v_flipped_boxed_5760_,
        v_heq_boxed_5761_,
        v_a_5749_,
        v_a_5750_,
        v_a_5751_,
        v_a_5752_,
        v_a_5753_,
        v_a_5754_,
        v_a_5755_,
        v_a_5756_,
        v_a_5757_,
        v_a_5758_,
    );
    lean_dec(v_a_5758_);
    lean_dec_ref(v_a_5757_);
    lean_dec(v_a_5756_);
    lean_dec_ref(v_a_5755_);
    lean_dec(v_a_5754_);
    lean_dec_ref(v_a_5753_);
    lean_dec(v_a_5752_);
    lean_dec_ref(v_a_5751_);
    lean_dec(v_a_5750_);
    lean_dec(v_a_5749_);
    return v_res_5762_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof___boxed(
    mut v_lhs_5763_: *mut LeanObject,
    mut v_rhs_5764_: *mut LeanObject,
    mut v_heq_5765_: *mut LeanObject,
    mut v_a_5766_: *mut LeanObject,
    mut v_a_5767_: *mut LeanObject,
    mut v_a_5768_: *mut LeanObject,
    mut v_a_5769_: *mut LeanObject,
    mut v_a_5770_: *mut LeanObject,
    mut v_a_5771_: *mut LeanObject,
    mut v_a_5772_: *mut LeanObject,
    mut v_a_5773_: *mut LeanObject,
    mut v_a_5774_: *mut LeanObject,
    mut v_a_5775_: *mut LeanObject,
    mut v_a_5776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5777_: u8 = 0;
    let mut v_res_5778_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5777_ = (lean_unbox(v_heq_5765_) as u8);
    v_res_5778_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof(
        v_lhs_5763_,
        v_rhs_5764_,
        v_heq_boxed_5777_,
        v_a_5766_,
        v_a_5767_,
        v_a_5768_,
        v_a_5769_,
        v_a_5770_,
        v_a_5771_,
        v_a_5772_,
        v_a_5773_,
        v_a_5774_,
        v_a_5775_,
    );
    lean_dec(v_a_5775_);
    lean_dec_ref(v_a_5774_);
    lean_dec(v_a_5773_);
    lean_dec_ref(v_a_5772_);
    lean_dec(v_a_5771_);
    lean_dec_ref(v_a_5770_);
    lean_dec(v_a_5769_);
    lean_dec_ref(v_a_5768_);
    lean_dec(v_a_5767_);
    lean_dec(v_a_5766_);
    lean_dec_ref(v_rhs_5764_);
    lean_dec_ref(v_lhs_5763_);
    return v_res_5778_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper___boxed(
    mut v_thm_5779_: *mut LeanObject,
    mut v_lhs_5780_: *mut LeanObject,
    mut v_rhs_5781_: *mut LeanObject,
    mut v_i_5782_: *mut LeanObject,
    mut v_a_5783_: *mut LeanObject,
    mut v_a_5784_: *mut LeanObject,
    mut v_a_5785_: *mut LeanObject,
    mut v_a_5786_: *mut LeanObject,
    mut v_a_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
    mut v_a_5789_: *mut LeanObject,
    mut v_a_5790_: *mut LeanObject,
    mut v_a_5791_: *mut LeanObject,
    mut v_a_5792_: *mut LeanObject,
    mut v_a_5793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5794_: *mut LeanObject = core::ptr::null_mut();
    v_res_5794_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProofHelper(
        v_thm_5779_,
        v_lhs_5780_,
        v_rhs_5781_,
        v_i_5782_,
        v_a_5783_,
        v_a_5784_,
        v_a_5785_,
        v_a_5786_,
        v_a_5787_,
        v_a_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
        v_a_5792_,
    );
    lean_dec(v_a_5792_);
    lean_dec_ref(v_a_5791_);
    lean_dec(v_a_5790_);
    lean_dec_ref(v_a_5789_);
    lean_dec(v_a_5788_);
    lean_dec_ref(v_a_5787_);
    lean_dec(v_a_5786_);
    lean_dec_ref(v_a_5785_);
    lean_dec(v_a_5784_);
    lean_dec(v_a_5783_);
    lean_dec(v_i_5782_);
    lean_dec_ref(v_rhs_5781_);
    lean_dec_ref(v_lhs_5780_);
    lean_dec_ref(v_thm_5779_);
    return v_res_5794_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_5795_: *mut LeanObject = *_args.add(0);
    let mut v_rhs_5796_: *mut LeanObject = *_args.add(1);
    let mut v_heq_5797_: *mut LeanObject = *_args.add(2);
    let mut v_e_u2081_5798_: *mut LeanObject = *_args.add(3);
    let mut v_e_u2082_5799_: *mut LeanObject = *_args.add(4);
    let mut v_numArgs_5800_: *mut LeanObject = *_args.add(5);
    let mut v_a_5801_: *mut LeanObject = *_args.add(6);
    let mut v_a_5802_: *mut LeanObject = *_args.add(7);
    let mut v_a_5803_: *mut LeanObject = *_args.add(8);
    let mut v_a_5804_: *mut LeanObject = *_args.add(9);
    let mut v_a_5805_: *mut LeanObject = *_args.add(10);
    let mut v_a_5806_: *mut LeanObject = *_args.add(11);
    let mut v_a_5807_: *mut LeanObject = *_args.add(12);
    let mut v_a_5808_: *mut LeanObject = *_args.add(13);
    let mut v_a_5809_: *mut LeanObject = *_args.add(14);
    let mut v_a_5810_: *mut LeanObject = *_args.add(15);
    let mut v_a_5811_: *mut LeanObject = *_args.add(16);
    let mut v_heq_boxed_5812_: u8 = 0;
    let mut v_res_5813_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5812_ = (lean_unbox(v_heq_5797_) as u8);
    v_res_5813_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProofFunCC_go(
        v_lhs_5795_,
        v_rhs_5796_,
        v_heq_boxed_5812_,
        v_e_u2081_5798_,
        v_e_u2082_5799_,
        v_numArgs_5800_,
        v_a_5801_,
        v_a_5802_,
        v_a_5803_,
        v_a_5804_,
        v_a_5805_,
        v_a_5806_,
        v_a_5807_,
        v_a_5808_,
        v_a_5809_,
        v_a_5810_,
    );
    lean_dec(v_a_5810_);
    lean_dec_ref(v_a_5809_);
    lean_dec(v_a_5808_);
    lean_dec_ref(v_a_5807_);
    lean_dec(v_a_5806_);
    lean_dec_ref(v_a_5805_);
    lean_dec(v_a_5804_);
    lean_dec_ref(v_a_5803_);
    lean_dec(v_a_5802_);
    lean_dec(v_a_5801_);
    return v_res_5813_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo___boxed(
    mut v_lhs_5814_: *mut LeanObject,
    mut v_common_5815_: *mut LeanObject,
    mut v_acc_5816_: *mut LeanObject,
    mut v_heq_5817_: *mut LeanObject,
    mut v_a_5818_: *mut LeanObject,
    mut v_a_5819_: *mut LeanObject,
    mut v_a_5820_: *mut LeanObject,
    mut v_a_5821_: *mut LeanObject,
    mut v_a_5822_: *mut LeanObject,
    mut v_a_5823_: *mut LeanObject,
    mut v_a_5824_: *mut LeanObject,
    mut v_a_5825_: *mut LeanObject,
    mut v_a_5826_: *mut LeanObject,
    mut v_a_5827_: *mut LeanObject,
    mut v_a_5828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5829_: u8 = 0;
    let mut v_res_5830_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5829_ = (lean_unbox(v_heq_5817_) as u8);
    v_res_5830_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofTo(
        v_lhs_5814_,
        v_common_5815_,
        v_acc_5816_,
        v_heq_boxed_5829_,
        v_a_5818_,
        v_a_5819_,
        v_a_5820_,
        v_a_5821_,
        v_a_5822_,
        v_a_5823_,
        v_a_5824_,
        v_a_5825_,
        v_a_5826_,
        v_a_5827_,
    );
    lean_dec(v_a_5827_);
    lean_dec_ref(v_a_5826_);
    lean_dec(v_a_5825_);
    lean_dec_ref(v_a_5824_);
    lean_dec(v_a_5823_);
    lean_dec_ref(v_a_5822_);
    lean_dec(v_a_5821_);
    lean_dec_ref(v_a_5820_);
    lean_dec(v_a_5819_);
    lean_dec(v_a_5818_);
    lean_dec_ref(v_common_5815_);
    return v_res_5830_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_5831_: *mut LeanObject = *_args.add(0);
    let mut v_g_5832_: *mut LeanObject = *_args.add(1);
    let mut v_numArgs_5833_: *mut LeanObject = *_args.add(2);
    let mut v_lhs_5834_: *mut LeanObject = *_args.add(3);
    let mut v_rhs_5835_: *mut LeanObject = *_args.add(4);
    let mut v_heq_5836_: *mut LeanObject = *_args.add(5);
    let mut v_a_5837_: *mut LeanObject = *_args.add(6);
    let mut v_a_5838_: *mut LeanObject = *_args.add(7);
    let mut v_a_5839_: *mut LeanObject = *_args.add(8);
    let mut v_a_5840_: *mut LeanObject = *_args.add(9);
    let mut v_a_5841_: *mut LeanObject = *_args.add(10);
    let mut v_a_5842_: *mut LeanObject = *_args.add(11);
    let mut v_a_5843_: *mut LeanObject = *_args.add(12);
    let mut v_a_5844_: *mut LeanObject = *_args.add(13);
    let mut v_a_5845_: *mut LeanObject = *_args.add(14);
    let mut v_a_5846_: *mut LeanObject = *_args.add(15);
    let mut v_a_5847_: *mut LeanObject = *_args.add(16);
    let mut v_heq_boxed_5848_: u8 = 0;
    let mut v_res_5849_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5848_ = (lean_unbox(v_heq_5836_) as u8);
    v_res_5849_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27(
        v_f_5831_,
        v_g_5832_,
        v_numArgs_5833_,
        v_lhs_5834_,
        v_rhs_5835_,
        v_heq_boxed_5848_,
        v_a_5837_,
        v_a_5838_,
        v_a_5839_,
        v_a_5840_,
        v_a_5841_,
        v_a_5842_,
        v_a_5843_,
        v_a_5844_,
        v_a_5845_,
        v_a_5846_,
    );
    lean_dec(v_a_5846_);
    lean_dec_ref(v_a_5845_);
    lean_dec(v_a_5844_);
    lean_dec_ref(v_a_5843_);
    lean_dec(v_a_5842_);
    lean_dec_ref(v_a_5841_);
    lean_dec(v_a_5840_);
    lean_dec_ref(v_a_5839_);
    lean_dec(v_a_5838_);
    lean_dec(v_a_5837_);
    return v_res_5849_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom___boxed(
    mut v_rhs_5850_: *mut LeanObject,
    mut v_common_5851_: *mut LeanObject,
    mut v_lhsEqCommon_x3f_5852_: *mut LeanObject,
    mut v_heq_5853_: *mut LeanObject,
    mut v_a_5854_: *mut LeanObject,
    mut v_a_5855_: *mut LeanObject,
    mut v_a_5856_: *mut LeanObject,
    mut v_a_5857_: *mut LeanObject,
    mut v_a_5858_: *mut LeanObject,
    mut v_a_5859_: *mut LeanObject,
    mut v_a_5860_: *mut LeanObject,
    mut v_a_5861_: *mut LeanObject,
    mut v_a_5862_: *mut LeanObject,
    mut v_a_5863_: *mut LeanObject,
    mut v_a_5864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5865_: u8 = 0;
    let mut v_res_5866_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5865_ = (lean_unbox(v_heq_5853_) as u8);
    v_res_5866_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkProofFrom(
        v_rhs_5850_,
        v_common_5851_,
        v_lhsEqCommon_x3f_5852_,
        v_heq_boxed_5865_,
        v_a_5854_,
        v_a_5855_,
        v_a_5856_,
        v_a_5857_,
        v_a_5858_,
        v_a_5859_,
        v_a_5860_,
        v_a_5861_,
        v_a_5862_,
        v_a_5863_,
    );
    lean_dec(v_a_5863_);
    lean_dec_ref(v_a_5862_);
    lean_dec(v_a_5861_);
    lean_dec_ref(v_a_5860_);
    lean_dec(v_a_5859_);
    lean_dec_ref(v_a_5858_);
    lean_dec(v_a_5857_);
    lean_dec_ref(v_a_5856_);
    lean_dec(v_a_5855_);
    lean_dec(v_a_5854_);
    lean_dec_ref(v_common_5851_);
    return v_res_5866_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop___boxed(
    mut v_lhs_5867_: *mut LeanObject,
    mut v_rhs_5868_: *mut LeanObject,
    mut v_a_5869_: *mut LeanObject,
    mut v_a_5870_: *mut LeanObject,
    mut v_a_5871_: *mut LeanObject,
    mut v_a_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
    mut v_a_5874_: *mut LeanObject,
    mut v_a_5875_: *mut LeanObject,
    mut v_a_5876_: *mut LeanObject,
    mut v_a_5877_: *mut LeanObject,
    mut v_a_5878_: *mut LeanObject,
    mut v_a_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5880_: *mut LeanObject = core::ptr::null_mut();
    v_res_5880_ =
        l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrDefaultProof_loop(
            v_lhs_5867_,
            v_rhs_5868_,
            v_a_5869_,
            v_a_5870_,
            v_a_5871_,
            v_a_5872_,
            v_a_5873_,
            v_a_5874_,
            v_a_5875_,
            v_a_5876_,
            v_a_5877_,
            v_a_5878_,
        );
    lean_dec(v_a_5878_);
    lean_dec_ref(v_a_5877_);
    lean_dec(v_a_5876_);
    lean_dec_ref(v_a_5875_);
    lean_dec(v_a_5874_);
    lean_dec_ref(v_a_5873_);
    lean_dec(v_a_5872_);
    lean_dec_ref(v_a_5871_);
    lean_dec(v_a_5870_);
    lean_dec(v_a_5869_);
    lean_dec_ref(v_rhs_5868_);
    lean_dec_ref(v_lhs_5867_);
    return v_res_5880_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof___boxed(
    mut v_lhs_5881_: *mut LeanObject,
    mut v_rhs_5882_: *mut LeanObject,
    mut v_heq_5883_: *mut LeanObject,
    mut v_a_5884_: *mut LeanObject,
    mut v_a_5885_: *mut LeanObject,
    mut v_a_5886_: *mut LeanObject,
    mut v_a_5887_: *mut LeanObject,
    mut v_a_5888_: *mut LeanObject,
    mut v_a_5889_: *mut LeanObject,
    mut v_a_5890_: *mut LeanObject,
    mut v_a_5891_: *mut LeanObject,
    mut v_a_5892_: *mut LeanObject,
    mut v_a_5893_: *mut LeanObject,
    mut v_a_5894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5895_: u8 = 0;
    let mut v_res_5896_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5895_ = (lean_unbox(v_heq_5883_) as u8);
    v_res_5896_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof(
        v_lhs_5881_,
        v_rhs_5882_,
        v_heq_boxed_5895_,
        v_a_5884_,
        v_a_5885_,
        v_a_5886_,
        v_a_5887_,
        v_a_5888_,
        v_a_5889_,
        v_a_5890_,
        v_a_5891_,
        v_a_5892_,
        v_a_5893_,
    );
    lean_dec(v_a_5893_);
    lean_dec_ref(v_a_5892_);
    lean_dec(v_a_5891_);
    lean_dec_ref(v_a_5890_);
    lean_dec(v_a_5889_);
    lean_dec_ref(v_a_5888_);
    lean_dec(v_a_5887_);
    lean_dec_ref(v_a_5886_);
    lean_dec(v_a_5885_);
    lean_dec(v_a_5884_);
    return v_res_5896_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore___boxed(
    mut v_lhs_5897_: *mut LeanObject,
    mut v_rhs_5898_: *mut LeanObject,
    mut v_heq_5899_: *mut LeanObject,
    mut v_a_5900_: *mut LeanObject,
    mut v_a_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_a_5903_: *mut LeanObject,
    mut v_a_5904_: *mut LeanObject,
    mut v_a_5905_: *mut LeanObject,
    mut v_a_5906_: *mut LeanObject,
    mut v_a_5907_: *mut LeanObject,
    mut v_a_5908_: *mut LeanObject,
    mut v_a_5909_: *mut LeanObject,
    mut v_a_5910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5911_: u8 = 0;
    let mut v_res_5912_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5911_ = (lean_unbox(v_heq_5899_) as u8);
    v_res_5912_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
        v_lhs_5897_,
        v_rhs_5898_,
        v_heq_boxed_5911_,
        v_a_5900_,
        v_a_5901_,
        v_a_5902_,
        v_a_5903_,
        v_a_5904_,
        v_a_5905_,
        v_a_5906_,
        v_a_5907_,
        v_a_5908_,
        v_a_5909_,
    );
    lean_dec(v_a_5909_);
    lean_dec_ref(v_a_5908_);
    lean_dec(v_a_5907_);
    lean_dec_ref(v_a_5906_);
    lean_dec(v_a_5905_);
    lean_dec_ref(v_a_5904_);
    lean_dec(v_a_5903_);
    lean_dec_ref(v_a_5902_);
    lean_dec(v_a_5901_);
    lean_dec(v_a_5900_);
    return v_res_5912_;
}
pub unsafe fn l_Lean_Meta_Grind_mkEqCongrProof___boxed(
    mut v_lhs_5913_: *mut LeanObject,
    mut v_rhs_5914_: *mut LeanObject,
    mut v_a_5915_: *mut LeanObject,
    mut v_a_5916_: *mut LeanObject,
    mut v_a_5917_: *mut LeanObject,
    mut v_a_5918_: *mut LeanObject,
    mut v_a_5919_: *mut LeanObject,
    mut v_a_5920_: *mut LeanObject,
    mut v_a_5921_: *mut LeanObject,
    mut v_a_5922_: *mut LeanObject,
    mut v_a_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5926_: *mut LeanObject = core::ptr::null_mut();
    v_res_5926_ = l_Lean_Meta_Grind_mkEqCongrProof(
        v_lhs_5913_,
        v_rhs_5914_,
        v_a_5915_,
        v_a_5916_,
        v_a_5917_,
        v_a_5918_,
        v_a_5919_,
        v_a_5920_,
        v_a_5921_,
        v_a_5922_,
        v_a_5923_,
        v_a_5924_,
    );
    lean_dec(v_a_5924_);
    lean_dec_ref(v_a_5923_);
    lean_dec(v_a_5922_);
    lean_dec_ref(v_a_5921_);
    lean_dec(v_a_5920_);
    lean_dec_ref(v_a_5919_);
    lean_dec(v_a_5918_);
    lean_dec_ref(v_a_5917_);
    lean_dec(v_a_5916_);
    lean_dec(v_a_5915_);
    return v_res_5926_;
}
pub unsafe fn l_Lean_Meta_Grind_mkEqCongrSymmProof___boxed(
    mut v_lhs_5927_: *mut LeanObject,
    mut v_rhs_5928_: *mut LeanObject,
    mut v_a_5929_: *mut LeanObject,
    mut v_a_5930_: *mut LeanObject,
    mut v_a_5931_: *mut LeanObject,
    mut v_a_5932_: *mut LeanObject,
    mut v_a_5933_: *mut LeanObject,
    mut v_a_5934_: *mut LeanObject,
    mut v_a_5935_: *mut LeanObject,
    mut v_a_5936_: *mut LeanObject,
    mut v_a_5937_: *mut LeanObject,
    mut v_a_5938_: *mut LeanObject,
    mut v_a_5939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5940_: *mut LeanObject = core::ptr::null_mut();
    v_res_5940_ = l_Lean_Meta_Grind_mkEqCongrSymmProof(
        v_lhs_5927_,
        v_rhs_5928_,
        v_a_5929_,
        v_a_5930_,
        v_a_5931_,
        v_a_5932_,
        v_a_5933_,
        v_a_5934_,
        v_a_5935_,
        v_a_5936_,
        v_a_5937_,
        v_a_5938_,
    );
    lean_dec(v_a_5938_);
    lean_dec_ref(v_a_5937_);
    lean_dec(v_a_5936_);
    lean_dec_ref(v_a_5935_);
    lean_dec(v_a_5934_);
    lean_dec_ref(v_a_5933_);
    lean_dec(v_a_5932_);
    lean_dec_ref(v_a_5931_);
    lean_dec(v_a_5930_);
    lean_dec(v_a_5929_);
    return v_res_5940_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof___boxed(
    mut v_lhs_5941_: *mut LeanObject,
    mut v_rhs_5942_: *mut LeanObject,
    mut v_heq_5943_: *mut LeanObject,
    mut v_a_5944_: *mut LeanObject,
    mut v_a_5945_: *mut LeanObject,
    mut v_a_5946_: *mut LeanObject,
    mut v_a_5947_: *mut LeanObject,
    mut v_a_5948_: *mut LeanObject,
    mut v_a_5949_: *mut LeanObject,
    mut v_a_5950_: *mut LeanObject,
    mut v_a_5951_: *mut LeanObject,
    mut v_a_5952_: *mut LeanObject,
    mut v_a_5953_: *mut LeanObject,
    mut v_a_5954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_heq_boxed_5955_: u8 = 0;
    let mut v_res_5956_: *mut LeanObject = core::ptr::null_mut();
    v_heq_boxed_5955_ = (lean_unbox(v_heq_5943_) as u8);
    v_res_5956_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkCongrProof(
        v_lhs_5941_,
        v_rhs_5942_,
        v_heq_boxed_5955_,
        v_a_5944_,
        v_a_5945_,
        v_a_5946_,
        v_a_5947_,
        v_a_5948_,
        v_a_5949_,
        v_a_5950_,
        v_a_5951_,
        v_a_5952_,
        v_a_5953_,
    );
    lean_dec(v_a_5953_);
    lean_dec_ref(v_a_5952_);
    lean_dec(v_a_5951_);
    lean_dec_ref(v_a_5950_);
    lean_dec(v_a_5949_);
    lean_dec_ref(v_a_5948_);
    lean_dec(v_a_5947_);
    lean_dec_ref(v_a_5946_);
    lean_dec(v_a_5945_);
    lean_dec(v_a_5944_);
    return v_res_5956_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(
    mut v_00_u03b1_5957_: *mut LeanObject,
    mut v_ref_5958_: *mut LeanObject,
    mut v___y_5959_: *mut LeanObject,
    mut v___y_5960_: *mut LeanObject,
    mut v___y_5961_: *mut LeanObject,
    mut v___y_5962_: *mut LeanObject,
    mut v___y_5963_: *mut LeanObject,
    mut v___y_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
    mut v___y_5968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    v___x_5970_ =
        l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___redArg(
            v_ref_5958_,
        );
    return v___x_5970_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7___boxed(
    mut v_00_u03b1_5971_: *mut LeanObject,
    mut v_ref_5972_: *mut LeanObject,
    mut v___y_5973_: *mut LeanObject,
    mut v___y_5974_: *mut LeanObject,
    mut v___y_5975_: *mut LeanObject,
    mut v___y_5976_: *mut LeanObject,
    mut v___y_5977_: *mut LeanObject,
    mut v___y_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5984_: *mut LeanObject = core::ptr::null_mut();
    v_res_5984_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_mkEqCongrSymmProof_spec__7(
        v_00_u03b1_5971_,
        v_ref_5972_,
        v___y_5973_,
        v___y_5974_,
        v___y_5975_,
        v___y_5976_,
        v___y_5977_,
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
    lean_dec(v___y_5978_);
    lean_dec_ref(v___y_5977_);
    lean_dec(v___y_5976_);
    lean_dec_ref(v___y_5975_);
    lean_dec(v___y_5974_);
    lean_dec(v___y_5973_);
    return v_res_5984_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(
    mut v_00_u03b1_5985_: *mut LeanObject,
    mut v_name_5986_: *mut LeanObject,
    mut v_bi_5987_: u8,
    mut v_type_5988_: *mut LeanObject,
    mut v_k_5989_: *mut LeanObject,
    mut v_kind_5990_: u8,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    v___x_6002_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___redArg(v_name_5986_, v_bi_5987_, v_type_5988_, v_k_5989_, v_kind_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_);
    return v___x_6002_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_6003_: *mut LeanObject = *_args.add(0);
    let mut v_name_6004_: *mut LeanObject = *_args.add(1);
    let mut v_bi_6005_: *mut LeanObject = *_args.add(2);
    let mut v_type_6006_: *mut LeanObject = *_args.add(3);
    let mut v_k_6007_: *mut LeanObject = *_args.add(4);
    let mut v_kind_6008_: *mut LeanObject = *_args.add(5);
    let mut v___y_6009_: *mut LeanObject = *_args.add(6);
    let mut v___y_6010_: *mut LeanObject = *_args.add(7);
    let mut v___y_6011_: *mut LeanObject = *_args.add(8);
    let mut v___y_6012_: *mut LeanObject = *_args.add(9);
    let mut v___y_6013_: *mut LeanObject = *_args.add(10);
    let mut v___y_6014_: *mut LeanObject = *_args.add(11);
    let mut v___y_6015_: *mut LeanObject = *_args.add(12);
    let mut v___y_6016_: *mut LeanObject = *_args.add(13);
    let mut v___y_6017_: *mut LeanObject = *_args.add(14);
    let mut v___y_6018_: *mut LeanObject = *_args.add(15);
    let mut v___y_6019_: *mut LeanObject = *_args.add(16);
    let mut v_bi_boxed_6020_: u8 = 0;
    let mut v_kind_boxed_6021_: u8 = 0;
    let mut v_res_6022_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_6020_ = (lean_unbox(v_bi_6005_) as u8);
    v_kind_boxed_6021_ = (lean_unbox(v_kind_6008_) as u8);
    v_res_6022_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1_spec__7(v_00_u03b1_6003_, v_name_6004_, v_bi_boxed_6020_, v_type_6006_, v_k_6007_, v_kind_boxed_6021_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_);
    lean_dec(v___y_6018_);
    lean_dec_ref(v___y_6017_);
    lean_dec(v___y_6016_);
    lean_dec_ref(v___y_6015_);
    lean_dec(v___y_6014_);
    lean_dec_ref(v___y_6013_);
    lean_dec(v___y_6012_);
    lean_dec_ref(v___y_6011_);
    lean_dec(v___y_6010_);
    lean_dec(v___y_6009_);
    return v_res_6022_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(
    mut v_00_u03b1_6023_: *mut LeanObject,
    mut v_name_6024_: *mut LeanObject,
    mut v_type_6025_: *mut LeanObject,
    mut v_k_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
    mut v___y_6036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    v___x_6038_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___redArg(v_name_6024_, v_type_6025_, v_k_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
    return v___x_6038_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1___boxed(
    mut v_00_u03b1_6039_: *mut LeanObject,
    mut v_name_6040_: *mut LeanObject,
    mut v_type_6041_: *mut LeanObject,
    mut v_k_6042_: *mut LeanObject,
    mut v___y_6043_: *mut LeanObject,
    mut v___y_6044_: *mut LeanObject,
    mut v___y_6045_: *mut LeanObject,
    mut v___y_6046_: *mut LeanObject,
    mut v___y_6047_: *mut LeanObject,
    mut v___y_6048_: *mut LeanObject,
    mut v___y_6049_: *mut LeanObject,
    mut v___y_6050_: *mut LeanObject,
    mut v___y_6051_: *mut LeanObject,
    mut v___y_6052_: *mut LeanObject,
    mut v___y_6053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6054_: *mut LeanObject = core::ptr::null_mut();
    v_res_6054_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_x27_spec__1(v_00_u03b1_6039_, v_name_6040_, v_type_6041_, v_k_6042_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_);
    lean_dec(v___y_6052_);
    lean_dec_ref(v___y_6051_);
    lean_dec(v___y_6050_);
    lean_dec_ref(v___y_6049_);
    lean_dec(v___y_6048_);
    lean_dec_ref(v___y_6047_);
    lean_dec(v___y_6046_);
    lean_dec_ref(v___y_6045_);
    lean_dec(v___y_6044_);
    lean_dec(v___y_6043_);
    return v_res_6054_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(
    mut v_00_u03b1_6055_: *mut LeanObject,
    mut v_msg_6056_: *mut LeanObject,
    mut v___y_6057_: *mut LeanObject,
    mut v___y_6058_: *mut LeanObject,
    mut v___y_6059_: *mut LeanObject,
    mut v___y_6060_: *mut LeanObject,
    mut v___y_6061_: *mut LeanObject,
    mut v___y_6062_: *mut LeanObject,
    mut v___y_6063_: *mut LeanObject,
    mut v___y_6064_: *mut LeanObject,
    mut v___y_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    v___x_6068_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v_msg_6056_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
    return v___x_6068_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___boxed(
    mut v_00_u03b1_6069_: *mut LeanObject,
    mut v_msg_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
    mut v___y_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6082_: *mut LeanObject = core::ptr::null_mut();
    v_res_6082_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10(v_00_u03b1_6069_, v_msg_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    lean_dec(v___y_6080_);
    lean_dec_ref(v___y_6079_);
    lean_dec(v___y_6078_);
    lean_dec_ref(v___y_6077_);
    lean_dec(v___y_6076_);
    lean_dec_ref(v___y_6075_);
    lean_dec(v___y_6074_);
    lean_dec_ref(v___y_6073_);
    lean_dec(v___y_6072_);
    lean_dec(v___y_6071_);
    return v_res_6082_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1() -> *mut LeanObject {
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    v___x_6084_ = l_Lean_Meta_Grind_mkEqProofImpl___closed__0;
    v___x_6085_ = l_Lean_stringToMessageData(v___x_6084_);
    return v___x_6085_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3() -> *mut LeanObject {
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    v___x_6087_ = l_Lean_Meta_Grind_mkEqProofImpl___closed__2;
    v___x_6088_ = l_Lean_stringToMessageData(v___x_6087_);
    return v___x_6088_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5() -> *mut LeanObject {
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    v___x_6090_ = l_Lean_Meta_Grind_mkEqProofImpl___closed__4;
    v___x_6091_ = l_Lean_stringToMessageData(v___x_6090_);
    return v___x_6091_;
}
pub unsafe fn lean_grind_mk_eq_proof(
    mut v_a_6092_: *mut LeanObject,
    mut v_b_6093_: *mut LeanObject,
    mut v_a_6094_: *mut LeanObject,
    mut v_a_6095_: *mut LeanObject,
    mut v_a_6096_: *mut LeanObject,
    mut v_a_6097_: *mut LeanObject,
    mut v_a_6098_: *mut LeanObject,
    mut v_a_6099_: *mut LeanObject,
    mut v_a_6100_: *mut LeanObject,
    mut v_a_6101_: *mut LeanObject,
    mut v_a_6102_: *mut LeanObject,
    mut v_a_6103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: u8 = 0;
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: u8 = 0;
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6147_: u8 = 0;
    let mut v_a_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6151_: u8 = 0;
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_b_6093_);
                lean_inc_ref(v_a_6092_);
                v___x_6118_ = l_Lean_Meta_Grind_hasSameType(
                    v_a_6092_, v_b_6093_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_,
                );
                if lean_obj_tag(v___x_6118_) == 0 {
                    v_a_6119_ = lean_ctor_get(v___x_6118_, 0);
                    lean_inc(v_a_6119_);
                    lean_dec_ref_known(v___x_6118_, 1);
                    v___x_6120_ = (lean_unbox(v_a_6119_) as u8);
                    lean_dec(v_a_6119_);
                    if v___x_6120_ == 0 {
                        lean_dec(v_a_6099_);
                        lean_dec_ref(v_a_6098_);
                        lean_dec(v_a_6097_);
                        lean_dec_ref(v_a_6096_);
                        lean_dec(v_a_6095_);
                        lean_dec(v_a_6094_);
                        lean_inc(v_a_6103_);
                        lean_inc_ref(v_a_6102_);
                        lean_inc(v_a_6101_);
                        lean_inc_ref(v_a_6100_);
                        lean_inc_ref(v_a_6092_);
                        v___x_6121_ =
                            lean_infer_type(v_a_6092_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_);
                        if lean_obj_tag(v___x_6121_) == 0 {
                            v_a_6122_ = lean_ctor_get(v___x_6121_, 0);
                            lean_inc(v_a_6122_);
                            lean_dec_ref_known(v___x_6121_, 1);
                            lean_inc(v_a_6103_);
                            lean_inc_ref(v_a_6102_);
                            lean_inc(v_a_6101_);
                            lean_inc_ref(v_a_6100_);
                            lean_inc_ref(v_b_6093_);
                            v___x_6123_ = lean_infer_type(
                                v_b_6093_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_,
                            );
                            if lean_obj_tag(v___x_6123_) == 0 {
                                v_a_6124_ = lean_ctor_get(v___x_6123_, 0);
                                lean_inc(v_a_6124_);
                                lean_dec_ref_known(v___x_6123_, 1);
                                v___x_6125_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkEqProofImpl___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkEqProofImpl___closed__1_once
                                    ),
                                    _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__1,
                                );
                                v___x_6126_ = l_Lean_indentExpr(v_a_6092_);
                                v___x_6127_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6127_, 0, v___x_6125_);
                                lean_ctor_set(v___x_6127_, 1, v___x_6126_);
                                v___x_6128_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkEqProofImpl___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkEqProofImpl___closed__3_once
                                    ),
                                    _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__3,
                                );
                                v___x_6129_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6129_, 0, v___x_6127_);
                                lean_ctor_set(v___x_6129_, 1, v___x_6128_);
                                v___x_6130_ = l_Lean_indentExpr(v_a_6122_);
                                v___x_6131_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6131_, 0, v___x_6129_);
                                lean_ctor_set(v___x_6131_, 1, v___x_6130_);
                                v___x_6132_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkEqProofImpl___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkEqProofImpl___closed__5_once
                                    ),
                                    _init_l_Lean_Meta_Grind_mkEqProofImpl___closed__5,
                                );
                                v___x_6133_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6133_, 0, v___x_6131_);
                                lean_ctor_set(v___x_6133_, 1, v___x_6132_);
                                v___x_6134_ = l_Lean_indentExpr(v_b_6093_);
                                v___x_6135_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6135_, 0, v___x_6133_);
                                lean_ctor_set(v___x_6135_, 1, v___x_6134_);
                                v___x_6136_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6136_, 0, v___x_6135_);
                                lean_ctor_set(v___x_6136_, 1, v___x_6128_);
                                v___x_6137_ = l_Lean_indentExpr(v_a_6124_);
                                v___x_6138_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_6138_, 0, v___x_6136_);
                                lean_ctor_set(v___x_6138_, 1, v___x_6137_);
                                v___x_6139_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__10___redArg(v___x_6138_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_);
                                lean_dec(v_a_6103_);
                                lean_dec_ref(v_a_6102_);
                                lean_dec(v_a_6101_);
                                lean_dec_ref(v_a_6100_);
                                v_a_6140_ = lean_ctor_get(v___x_6139_, 0);
                                v_isSharedCheck_6147_ = (!lean_is_exclusive(v___x_6139_)) as u8;
                                if v_isSharedCheck_6147_ == 0 {
                                    v___x_6142_ = v___x_6139_;
                                    v_isShared_6143_ = v_isSharedCheck_6147_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_6140_);
                                    lean_dec(v___x_6139_);
                                    v___x_6142_ = lean_box(0);
                                    v_isShared_6143_ = v_isSharedCheck_6147_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6122_);
                                lean_dec(v_a_6103_);
                                lean_dec_ref(v_a_6102_);
                                lean_dec(v_a_6101_);
                                lean_dec_ref(v_a_6100_);
                                lean_dec_ref(v_b_6093_);
                                lean_dec_ref(v_a_6092_);
                                return v___x_6123_;
                            }
                        } else {
                            lean_dec(v_a_6103_);
                            lean_dec_ref(v_a_6102_);
                            lean_dec(v_a_6101_);
                            lean_dec_ref(v_a_6100_);
                            lean_dec_ref(v_b_6093_);
                            lean_dec_ref(v_a_6092_);
                            return v___x_6121_;
                        }
                    } else {
                        v___y_6106_ = v_a_6094_;
                        v___y_6107_ = v_a_6095_;
                        v___y_6108_ = v_a_6096_;
                        v___y_6109_ = v_a_6097_;
                        v___y_6110_ = v_a_6098_;
                        v___y_6111_ = v_a_6099_;
                        v___y_6112_ = v_a_6100_;
                        v___y_6113_ = v_a_6101_;
                        v___y_6114_ = v_a_6102_;
                        v___y_6115_ = v_a_6103_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6103_);
                    lean_dec_ref(v_a_6102_);
                    lean_dec(v_a_6101_);
                    lean_dec_ref(v_a_6100_);
                    lean_dec(v_a_6099_);
                    lean_dec_ref(v_a_6098_);
                    lean_dec(v_a_6097_);
                    lean_dec_ref(v_a_6096_);
                    lean_dec(v_a_6095_);
                    lean_dec(v_a_6094_);
                    lean_dec_ref(v_b_6093_);
                    lean_dec_ref(v_a_6092_);
                    v_a_6148_ = lean_ctor_get(v___x_6118_, 0);
                    v_isSharedCheck_6155_ = (!lean_is_exclusive(v___x_6118_)) as u8;
                    if v_isSharedCheck_6155_ == 0 {
                        v___x_6150_ = v___x_6118_;
                        v_isShared_6151_ = v_isSharedCheck_6155_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6148_);
                        lean_dec(v___x_6118_);
                        v___x_6150_ = lean_box(0);
                        v_isShared_6151_ = v_isSharedCheck_6155_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6116_ = 0;
                v___x_6117_ =
                    l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
                        v_a_6092_,
                        v_b_6093_,
                        v___x_6116_,
                        v___y_6106_,
                        v___y_6107_,
                        v___y_6108_,
                        v___y_6109_,
                        v___y_6110_,
                        v___y_6111_,
                        v___y_6112_,
                        v___y_6113_,
                        v___y_6114_,
                        v___y_6115_,
                    );
                lean_dec(v___y_6115_);
                lean_dec_ref(v___y_6114_);
                lean_dec(v___y_6113_);
                lean_dec_ref(v___y_6112_);
                lean_dec(v___y_6111_);
                lean_dec_ref(v___y_6110_);
                lean_dec(v___y_6109_);
                lean_dec_ref(v___y_6108_);
                lean_dec(v___y_6107_);
                lean_dec(v___y_6106_);
                return v___x_6117_;
            }
            2 => {
                if v_isShared_6143_ == 0 {
                    v___x_6145_ = v___x_6142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_a_6140_);
                    v___x_6145_ = v_reuseFailAlloc_6146_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6145_;
            }
            4 => {
                if v_isShared_6151_ == 0 {
                    v___x_6153_ = v___x_6150_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
                    v___x_6153_ = v_reuseFailAlloc_6154_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkEqProofImpl___boxed(
    mut v_a_6156_: *mut LeanObject,
    mut v_b_6157_: *mut LeanObject,
    mut v_a_6158_: *mut LeanObject,
    mut v_a_6159_: *mut LeanObject,
    mut v_a_6160_: *mut LeanObject,
    mut v_a_6161_: *mut LeanObject,
    mut v_a_6162_: *mut LeanObject,
    mut v_a_6163_: *mut LeanObject,
    mut v_a_6164_: *mut LeanObject,
    mut v_a_6165_: *mut LeanObject,
    mut v_a_6166_: *mut LeanObject,
    mut v_a_6167_: *mut LeanObject,
    mut v_a_6168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6169_: *mut LeanObject = core::ptr::null_mut();
    v_res_6169_ = lean_grind_mk_eq_proof(
        v_a_6156_, v_b_6157_, v_a_6158_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_, v_a_6163_,
        v_a_6164_, v_a_6165_, v_a_6166_, v_a_6167_,
    );
    return v_res_6169_;
}
pub unsafe fn lean_grind_mk_heq_proof(
    mut v_a_6170_: *mut LeanObject,
    mut v_b_6171_: *mut LeanObject,
    mut v_a_6172_: *mut LeanObject,
    mut v_a_6173_: *mut LeanObject,
    mut v_a_6174_: *mut LeanObject,
    mut v_a_6175_: *mut LeanObject,
    mut v_a_6176_: *mut LeanObject,
    mut v_a_6177_: *mut LeanObject,
    mut v_a_6178_: *mut LeanObject,
    mut v_a_6179_: *mut LeanObject,
    mut v_a_6180_: *mut LeanObject,
    mut v_a_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6183_: u8 = 0;
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    v___x_6183_ = 1;
    v___x_6184_ = l___private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkEqProofCore(
        v_a_6170_,
        v_b_6171_,
        v___x_6183_,
        v_a_6172_,
        v_a_6173_,
        v_a_6174_,
        v_a_6175_,
        v_a_6176_,
        v_a_6177_,
        v_a_6178_,
        v_a_6179_,
        v_a_6180_,
        v_a_6181_,
    );
    lean_dec(v_a_6181_);
    lean_dec_ref(v_a_6180_);
    lean_dec(v_a_6179_);
    lean_dec_ref(v_a_6178_);
    lean_dec(v_a_6177_);
    lean_dec_ref(v_a_6176_);
    lean_dec(v_a_6175_);
    lean_dec_ref(v_a_6174_);
    lean_dec(v_a_6173_);
    lean_dec(v_a_6172_);
    return v___x_6184_;
}
pub unsafe fn l_Lean_Meta_Grind_mkHEqProofImpl___boxed(
    mut v_a_6185_: *mut LeanObject,
    mut v_b_6186_: *mut LeanObject,
    mut v_a_6187_: *mut LeanObject,
    mut v_a_6188_: *mut LeanObject,
    mut v_a_6189_: *mut LeanObject,
    mut v_a_6190_: *mut LeanObject,
    mut v_a_6191_: *mut LeanObject,
    mut v_a_6192_: *mut LeanObject,
    mut v_a_6193_: *mut LeanObject,
    mut v_a_6194_: *mut LeanObject,
    mut v_a_6195_: *mut LeanObject,
    mut v_a_6196_: *mut LeanObject,
    mut v_a_6197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6198_: *mut LeanObject = core::ptr::null_mut();
    v_res_6198_ = lean_grind_mk_heq_proof(
        v_a_6185_, v_b_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_,
        v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_,
    );
    return v_res_6198_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Proof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Proof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Proof(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
}
